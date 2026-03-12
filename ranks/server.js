const express=require('express'),app=express(),http=require('http'),server=http.createServer(app);
const{Server}=require('socket.io'),io=new Server(server);
const USERNAME=process.env.GAME_USERNAME,PASSWORD=process.env.GAME_PASSWORD;
app.use((req,res,next)=>{if(!USERNAME)return next();const b=(req.headers.authorization||'').split(' ')[1]||'';const[l,p]=Buffer.from(b,'base64').toString().split(':');if(l&&p&&l===USERNAME&&p===PASSWORD)return next();res.set('WWW-Authenticate','Basic realm="RANKS"');res.status(401).send('Auth required.');});
app.use(express.static('public'));

const N=7,PA=1,PB=2,QUAL=21;
function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}
function makeSupply(){const t=[];for(let v=1;v<=6;v++)for(let i=0;i<4;i++)t.push(v);return shuffle(t);}
function mkBoard(){return Array.from({length:N},()=>Array.from({length:N},()=>({owner:null,stack:[],faceUp:[]})));}
function inB(r,c){return r>=0&&r<N&&c>=0&&c<N;}
function orth(r,c){const o=[];for(const[dr,dc]of[[-1,0],[1,0],[0,-1],[0,1]]){const rr=r+dr,cc=c+dc;if(inB(rr,cc))o.push([rr,cc]);}return o;}
function mt(cl){return cl.owner===null||cl.stack.length===0;}
function ht(cl){return cl.stack.length;}
function fuScore(cl){let s=0;for(let i=0;i<cl.stack.length;i++)if(cl.faceUp[i])s+=cl.stack[i];return s;}

function mkState(rid){return{roomId:rid,board:mkBoard(),supplies:{[PA]:makeSupply(),[PB]:makeSupply()},currentPlayer:PA,phase:'PIE_PLACE',passesInRow:0,winner:null,winCondition:null,graveyard:[],ko:{[PA]:null,[PB]:null},lastMove:null,piePos:null,peekDone:false,peekedCells:{[PA]:new Set(),[PB]:new Set()},isAiGame:false,gameLog:[],metadata:{rid,p1_id:null,p2_id:null,start:Date.now()}};}

function occCells(b,p){const o=[];for(let r=0;r<N;r++)for(let c=0;c<N;c++)if(!mt(b[r][c])&&b[r][c].owner===p)o.push([r,c]);return o;}
function emptyCells(b){const o=[];for(let r=0;r<N;r++)for(let c=0;c<N;c++)if(mt(b[r][c]))o.push([r,c]);return o;}
function eAdj(b,p,r,c){const o=[];for(const[rr,cc]of orth(r,c))if(!mt(b[rr][cc])&&b[rr][cc].owner!==p)o.push([rr,cc]);return o;}
function hasStrikes(b,p){for(const[r,c]of occCells(b,p))if(eAdj(b,p,r,c).length>0)return true;return false;}

// Best path qual score: max face-up score along any simple path through player's tiles
function bestPathQual(b,p){
    const nodes=new Map();
    for(let r=0;r<N;r++)for(let c=0;c<N;c++){const cl=b[r][c];if(!mt(cl)&&cl.owner===p)nodes.set(`${r},${c}`,fuScore(cl));}
    if(!nodes.size)return 0;
    const adj={};for(const k of nodes.keys()){const[r,c]=k.split(',').map(Number);adj[k]=[];for(const[rr,cc]of orth(r,c)){const nk=`${rr},${cc}`;if(nodes.has(nk))adj[k].push(nk);}}
    let best=0,it=0;
    for(const sk of nodes.keys()){
        const stk=[{c:sk,seen:new Set([sk]),sc:nodes.get(sk)}];
        while(stk.length){if(++it>500000)return best;const{c:cur,seen,sc}=stk.pop();
            if(sc>best)best=sc;
            for(const nx of(adj[cur]||[]))if(!seen.has(nx)){const ns=new Set(seen);ns.add(nx);stk.push({c:nx,seen:ns,sc:sc+nodes.get(nx)});}}
    }
    return best;
}

// Qualified connection check (path from edge to edge with score >= QUAL)
function checkQC(b,p){
    const nodes=new Map();
    for(let r=0;r<N;r++)for(let c=0;c<N;c++){const cl=b[r][c];if(!mt(cl)&&cl.owner===p)nodes.set(`${r},${c}`,fuScore(cl));}
    if(!nodes.size)return false;
    const adj={};for(const k of nodes.keys()){const[r,c]=k.split(',').map(Number);adj[k]=[];for(const[rr,cc]of orth(r,c)){const nk=`${rr},${cc}`;if(nodes.has(nk))adj[k].push(nk);}}
    let it=0;
    function dfs(starts,goal){for(const s of starts){const stk=[{c:s,seen:new Set([s]),sc:nodes.get(s)}];while(stk.length){if(++it>500000)return false;const{c:cur,seen,sc}=stk.pop();if(goal(cur)&&sc>=QUAL)return true;for(const nx of(adj[cur]||[]))if(!seen.has(nx)){const ns=new Set(seen);ns.add(nx);stk.push({c:nx,seen:ns,sc:sc+nodes.get(nx)});}}}return false;}
    const rs=[];for(let c=0;c<N;c++)if(nodes.has(`0,${c}`))rs.push(`0,${c}`);
    if(rs.length&&dfs(rs,k=>k.split(',')[0]===String(N-1)))return true;
    const cs=[];for(let r=0;r<N;r++)if(nodes.has(`${r},0`))cs.push(`${r},0`);
    if(cs.length&&dfs(cs,k=>k.split(',')[1]===String(N-1)))return true;
    return false;
}

function checkExt(st){for(const p of[PA,PB])if(occCells(st.board,p).length===0&&st.supplies[p].length===0)return p;return null;}
function checkVic(st,atk){
    const c1=checkQC(st.board,PA),c2=checkQC(st.board,PB);
    if(c1&&c2){st.winner=atk||st.currentPlayer;st.winCondition='Qualified Connection (simultaneous)';st.phase='GAME_OVER';return true;}
    if(c1){st.winner=PA;st.winCondition='Qualified Connection';st.phase='GAME_OVER';return true;}
    if(c2){st.winner=PB;st.winCondition='Qualified Connection';st.phase='GAME_OVER';return true;}
    return false;
}

// Total face-up score (all tiles on board) - used for end scoring
function totalFU(b,p){let s=0;for(let r=0;r<N;r++)for(let c=0;c<N;c++){const cl=b[r][c];if(!mt(cl)&&cl.owner===p)s+=fuScore(cl);}return s;}

function finalByPass(st){
    const s1=totalFU(st.board,PA),s2=totalFU(st.board,PB);
    const t1=occCells(st.board,PA).length,t2=occCells(st.board,PB).length;
    st.phase='GAME_OVER';
    if(s1>s2)st.winner=PA;else if(s2>s1)st.winner=PB;else if(t1>t2)st.winner=PA;else if(t2>t1)st.winner=PB;else st.winner=null;
    st.winCondition=`Scoring (W:${s1} tiles:${t1} vs B:${s2} tiles:${t2})`;
}

function resolveStrike(st,p,aR,aC,tR,tC){
    const b=st.board,e=p===PA?PB:PA,ac=b[aR][aC];
    ac.faceUp[ac.stack.length-1]=true;
    const atkK=new Set([`${aR},${aC}`]);for(const[rr,cc]of orth(aR,aC))if(!mt(b[rr][cc])&&b[rr][cc].owner===p)atkK.add(`${rr},${cc}`);
    const defK=new Set([`${tR},${tC}`]);for(const[rr,cc]of orth(tR,tC))if(!mt(b[rr][cc])&&b[rr][cc].owner===e)defK.add(`${rr},${cc}`);
    for(const k of[...atkK,...defK]){const[r,c]=k.split(',').map(Number);b[r][c].faceUp=b[r][c].faceUp.map(()=>true);}
    let aS=0,dS=0;
    for(const k of atkK){const[r,c]=k.split(',').map(Number);aS+=b[r][c].stack.reduce((a,v)=>a+v,0);}
    for(const k of defK){const[r,c]=k.split(',').map(Number);dS+=b[r][c].stack.reduce((a,v)=>a+v,0);}
    st.gameLog.unshift(`P${p} strikes (${aR+1},${aC+1})->(${tR+1},${tC+1}): ATK ${aS} vs DEF ${dS}`);
    const cap=[];
    function capC(r,c){const cl=b[r][c];for(const v of cl.stack)st.graveyard.push({owner:cl.owner,value:v});cap.push({owner:cl.owner,r,c});cl.stack=[];cl.faceUp=[];cl.owner=null;}
    if(aS>dS){capC(tR,tC);st.gameLog.unshift(`  Defender captured at (${tR+1},${tC+1})`);}
    else if(dS>aS){capC(aR,aC);st.gameLog.unshift(`  Attacker captured at (${aR+1},${aC+1})`);}
    else{capC(aR,aC);capC(tR,tC);st.gameLog.unshift(`  Tie: both captured`);}
    st.ko={[PA]:null,[PB]:null};for(const cs of cap)st.ko[cs.owner]={r:cs.r,c:cs.c};
    st.lastMove={player:p,r:aR,c:aC};
    // Track captured cells for animation
    st.lastCaptures=cap.map(c=>({r:c.r,c:c.c,owner:c.owner}));
    const ext=checkExt(st);if(ext!==null){st.winner=ext===PA?PB:PA;st.winCondition='Extermination';st.phase='GAME_OVER';return;}
    checkVic(st,p);
}

function actDeploy(st,p,r,c){if(st.supplies[p].length===0)return false;if(!mt(st.board[r][c]))return false;if(st.ko[p]&&st.ko[p].r===r&&st.ko[p].c===c)return false;const v=st.supplies[p].shift();st.board[r][c]={owner:p,stack:[v],faceUp:[false]};st.lastMove={player:p,r,c};st.lastCaptures=[];st.ko={[PA]:null,[PB]:null};st.gameLog.unshift(`P${p} deploys at (${r+1},${c+1})`);checkVic(st);return true;}
function actReinforce(st,p,r,c){if(st.supplies[p].length===0)return false;const cl=st.board[r][c];if(mt(cl)||cl.owner!==p||ht(cl)!==1)return false;const v=st.supplies[p].shift();cl.stack.push(v);cl.faceUp.push(false);st.lastMove={player:p,r,c};st.lastCaptures=[];st.ko={[PA]:null,[PB]:null};st.gameLog.unshift(`P${p} reinforces at (${r+1},${c+1})`);checkVic(st);return true;}
function actStrike(st,p,aR,aC,tR,tC){const a=st.board[aR][aC],t=st.board[tR][tC];if(mt(a)||a.owner!==p)return false;if(mt(t)||t.owner===p)return false;if(Math.abs(aR-tR)+Math.abs(aC-tC)!==1)return false;resolveStrike(st,p,aR,aC,tR,tC);return true;}
function actPass(st,p){st.gameLog.unshift(`P${p} passes`);st.passesInRow++;st.ko={[PA]:null,[PB]:null};if(st.passesInRow>=2)finalByPass(st);}
function advTurn(st){if(st.phase==='GAME_OVER')return;st.currentPlayer=st.currentPlayer===PA?PB:PA;st.peekDone=false;st.phase='PEEK';}

function stateView(st,viewer){
    const bv=st.board.map(row=>row.map(cl=>{
        if(mt(cl))return{owner:null,tiles:[]};
        return{owner:cl.owner,height:ht(cl),
            tiles:cl.stack.map((v,i)=>({value:cl.faceUp[i]?v:null,faceUp:cl.faceUp[i],owner:cl.owner}))};
    }));
    // Peeked cells: send as array of "r,c" strings for the viewer
    const peekSet=st.peekedCells[viewer===PA?PB:PA];// opponent's peeked cells visible to us
    const oppPeeked=peekSet?[...peekSet]:[];
    return{board:bv,supplies:{[PA]:st.supplies[PA].length,[PB]:st.supplies[PB].length},
        myNextDraw:st.supplies[viewer]?.[0]??null,currentPlayer:st.currentPlayer,phase:st.phase,
        winner:st.winner,winCondition:st.winCondition,graveyard:st.graveyard,ko:st.ko,
        lastMove:st.lastMove,lastCaptures:st.lastCaptures||[],peekDone:st.peekDone,passesInRow:st.passesInRow,
        gameLog:st.gameLog.slice(0,50),isAiGame:st.isAiGame,qualThreshold:QUAL,boardSize:N,
        qualScores:{[PA]:bestPathQual(st.board,PA),[PB]:bestPathQual(st.board,PB)},
        oppPeeked,
    };
}

function bc(room){const st=room.state;if(room.p1&&room.p1!=='AI')io.to(room.p1).emit('update',stateView(st,PA));if(room.p2&&room.p2!=='AI')io.to(room.p2).emit('update',stateView(st,PB));}

// ═══ AI ═══
function bfsR(b,p,starts){const seen=new Set(starts.map(([r,c])=>`${r},${c}`));const q=[...starts];while(q.length){const[r,c]=q.shift();for(const[rr,cc]of orth(r,c)){const k=`${rr},${cc}`;if(!seen.has(k)&&!mt(b[rr][cc])&&b[rr][cc].owner===p){seen.add(k);q.push([rr,cc]);}}}return seen;}

function aiAxis(b,p){
    let bestA='row',bestP=-1,bestGap=N;
    // Row: top->bottom
    const top=[];for(let c=0;c<N;c++)if(!mt(b[0][c])&&b[0][c].owner===p)top.push([0,c]);
    if(top.length){const r=bfsR(b,p,top);let mx=0;for(const k of r)mx=Math.max(mx,parseInt(k));if(mx>=bestP){bestP=mx;bestA='row';bestGap=N-1-mx;}}
    // Row: bottom->top
    const bot=[];for(let c=0;c<N;c++)if(!mt(b[N-1][c])&&b[N-1][c].owner===p)bot.push([N-1,c]);
    if(bot.length){const r=bfsR(b,p,bot);let mn=N-1;for(const k of r)mn=Math.min(mn,parseInt(k));const prog=N-1-mn;if(prog>bestP){bestP=prog;bestA='row';bestGap=mn;}}
    // Col: left->right
    const left=[];for(let r=0;r<N;r++)if(!mt(b[r][0])&&b[r][0].owner===p)left.push([r,0]);
    if(left.length){const r=bfsR(b,p,left);let mx=0;for(const k of r)mx=Math.max(mx,parseInt(k.split(',')[1]));if(mx>bestP){bestP=mx;bestA='col';bestGap=N-1-mx;}}
    // Col: right->left
    const right=[];for(let r=0;r<N;r++)if(!mt(b[r][N-1])&&b[r][N-1].owner===p)right.push([r,N-1]);
    if(right.length){const r=bfsR(b,p,right);let mn=N-1;for(const k of r)mn=Math.min(mn,parseInt(k.split(',')[1]));const prog=N-1-mn;if(prog>bestP){bestP=prog;bestA='col';bestGap=mn;}}
    return{axis:bestA,progress:bestP,gap:bestGap};
}

function aiMove(st){
    const b=st.board,p=PB,e=PA,hasS=st.supplies[p].length>0;
    if(!hasS&&!hasStrikes(b,p))return{type:'pass'};
    if(!hasS)return aiBestStr(b,p);
    const fb=st.ko[p];
    // Win/block
    for(const[r,c]of emptyCells(b)){if(fb&&fb.r===r&&fb.c===c)continue;const s=JSON.parse(JSON.stringify(b));s[r][c]={owner:p,stack:[1],faceUp:[false]};if(checkQC(s,p))return{type:'deploy',r,c};}
    for(const[r,c]of emptyCells(b)){if(fb&&fb.r===r&&fb.c===c)continue;const s=JSON.parse(JSON.stringify(b));s[r][c]={owner:e,stack:[1],faceUp:[false]};if(checkQC(s,e))return{type:'deploy',r,c};}

    const myAx=aiAxis(b,p),eAx=aiAxis(b,e);
    const ownS=new Set(occCells(b,p).map(([r,c])=>`${r},${c}`));
    const ctr=(N-1)/2;
    const moves=[];

    for(const[r,c]of emptyCells(b)){
        if(fb&&fb.r===r&&fb.c===c)continue;
        let s=0;
        // Adjacency
        for(const[rr,cc]of orth(r,c))if(ownS.has(`${rr},${cc}`))s+=14;
        // Connection direction
        if(myAx.axis==='row'){
            if(r>myAx.progress)s+=20; // beyond frontier
            if(r===0||r===N-1)s+=10;
            s+=4*(3-Math.abs(c-ctr)); // center column
        }else{
            if(c>myAx.progress)s+=20;
            if(c===0||c===N-1)s+=10;
            s+=4*(3-Math.abs(r-ctr));
        }
        // Block enemy if they're close
        if(eAx.gap<=2){
            // Place near enemy frontier
            if(eAx.axis==='row'){const d=Math.abs(r-eAx.progress);if(d<=1)s+=18;}
            else{const d=Math.abs(c-eAx.progress);if(d<=1)s+=18;}
        }
        // Edge placement bonus for connection
        if(r===0||r===N-1)s+=6;if(c===0||c===N-1)s+=6;
        moves.push({type:'deploy',r,c,score:s});
    }
    for(const[r,c]of occCells(b,p))if(ht(b[r][c])===1){let s=eAdj(b,p,r,c).length*18-4;moves.push({type:'reinforce',r,c,score:s});}
    for(const[r,c]of occCells(b,p))for(const[tr,tc]of eAdj(b,p,r,c)){
        let aS=b[r][c].stack.reduce((a,v)=>a+v,0);for(const[rr,cc]of orth(r,c))if(!mt(b[rr][cc])&&b[rr][cc].owner===p)aS+=b[rr][cc].stack.reduce((a,v)=>a+v,0);
        let dS=b[tr][tc].stack.reduce((a,v)=>a+v,0);for(const[rr,cc]of orth(tr,tc))if(!mt(b[rr][cc])&&b[rr][cc].owner!==p)dS+=b[rr][cc].stack.reduce((a,v)=>a+v,0);
        let s=aS>dS?(aS-dS)*3+8:-(dS-aS)*4;
        // Bonus for removing blocking tiles
        if(myAx.axis==='row'&&Math.abs(tr-myAx.progress)<=1)s+=8;
        if(myAx.axis==='col'&&Math.abs(tc-myAx.progress)<=1)s+=8;
        moves.push({type:'strike',atkR:r,atkC:c,tgtR:tr,tgtC:tc,score:s});
    }
    if(!moves.length)return{type:'pass'};
    moves.sort((a,b)=>b.score-a.score);return moves[0];
}
function aiBestStr(b,p){const s=[];for(const[r,c]of occCells(b,p))for(const[tr,tc]of eAdj(b,p,r,c))s.push({type:'strike',atkR:r,atkC:c,tgtR:tr,tgtC:tc,score:b[r][c].stack.reduce((a,v)=>a+v,0)});s.sort((a,b)=>b.score-a.score);return s[0]||{type:'pass'};}

function execAI(st,room){
    if(st.currentPlayer!==PB||!st.isAiGame||st.phase==='GAME_OVER')return;
    if(st.phase==='PEEK')st.phase='ACTION';
    const mv=aiMove(st);
    if(mv.type==='deploy'){st.passesInRow=0;actDeploy(st,PB,mv.r,mv.c);}
    else if(mv.type==='reinforce'){st.passesInRow=0;actReinforce(st,PB,mv.r,mv.c);}
    else if(mv.type==='strike'){st.passesInRow=0;actStrike(st,PB,mv.atkR,mv.atkC,mv.tgtR,mv.tgtC);}
    else actPass(st,PB);
    if(st.phase!=='GAME_OVER')advTurn(st);bc(room);
}

const rooms={};
io.on('connection',(socket)=>{
    socket.on('joinGame',(irid)=>{let rid=String(irid).toUpperCase().trim();const ai=rid==='PLAYAI';if(ai)rid=`AI_${socket.id}`;
        if(!rooms[rid]){const st=mkState(rid);st.isAiGame=ai;st.metadata.p1_id=socket.id;st.metadata.p2_id=ai?'AI':null;rooms[rid]={state:st,p1:socket.id,p2:ai?'AI':null};socket.join(rid);socket.emit('init',{player:PA,roomId:rid});if(ai)socket.emit('update',stateView(st,PA));else socket.emit('waiting');}
        else if(rooms[rid].p2===null){rooms[rid].p2=socket.id;rooms[rid].state.metadata.p2_id=socket.id;socket.join(rid);socket.emit('init',{player:PB,roomId:rid});io.to(rooms[rid].p1).emit('init',{player:PA,roomId:rid});bc(rooms[rid]);}
        else socket.emit('roomFull');});
    socket.on('rejoinGame',({roomId:rid,player:pl})=>{const room=rooms[rid];if(!room){socket.emit('rejoinFailed','Not found');return;}if(room.state.phase==='GAME_OVER'){socket.emit('rejoinFailed','Over');return;}if(pl===PA){room.p1=socket.id;room.state.metadata.p1_id=socket.id;}else if(pl===PB&&room.p2!=='AI'){room.p2=socket.id;room.state.metadata.p2_id=socket.id;}else{socket.emit('rejoinFailed','Invalid');return;}socket.join(rid);socket.emit('init',{player:pl,roomId:rid});socket.emit('update',stateView(room.state,pl));});
    socket.on('action',(data)=>{const{roomId:rid,type,r,c,r2,c2,swap}=data;const room=rooms[rid];if(!room)return;const st=room.state;const pn=socket.id===room.p1?PA:(socket.id===room.p2?PB:null);if(pn===null)return;
        if(st.phase==='PIE_PLACE'&&pn===PA&&type==='place'){if(!mt(st.board[r][c]))return;const v=st.supplies[PA].shift();st.board[r][c]={owner:PA,stack:[v],faceUp:[false]};st.piePos={r,c};st.phase='PIE_DECISION';st.currentPlayer=PB;st.gameLog.unshift(`P1 opening at (${r+1},${c+1})`);if(st.isAiGame){st.gameLog.unshift('AI continues as Black.');st.phase='PEEK';st.currentPlayer=PB;bc(room);setTimeout(()=>execAI(st,room),600);}else bc(room);return;}
        if(st.phase==='PIE_DECISION'&&pn===PB&&type==='pieDecision'){if(swap){[room.p1,room.p2]=[room.p2,room.p1];st.metadata.p1_id=room.p1;st.metadata.p2_id=room.p2;st.currentPlayer=PB;st.gameLog.unshift('P2 swapped.');io.to(room.p1).emit('init',{player:PA,roomId:rid});io.to(room.p2).emit('init',{player:PB,roomId:rid});}else{st.currentPlayer=PB;st.gameLog.unshift('No swap.');}st.phase='PEEK';bc(room);return;}
        if(st.phase==='PEEK'&&pn===st.currentPlayer){if(type==='peek'){const cl=st.board[r][c];if(!mt(cl)&&cl.owner===pn){socket.emit('peekResult',{r,c,values:cl.stack});st.peekedCells[pn].add(`${r},${c}`);st.gameLog.unshift(`P${pn} peeks at (${r+1},${c+1})`);}}if(type==='skipPeek'||type==='peek'){st.peekDone=true;st.phase='ACTION';bc(room);return;}}
        if(st.phase==='ACTION'&&pn===st.currentPlayer){const se=st.supplies[pn].length===0;
            if(type==='deploy'&&!se){st.passesInRow=0;if(!actDeploy(st,pn,r,c))return;advTurn(st);bc(room);if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>execAI(st,room),600);return;}
            if(type==='reinforce'&&!se){st.passesInRow=0;if(!actReinforce(st,pn,r,c))return;advTurn(st);bc(room);if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>execAI(st,room),600);return;}
            if(type==='strike'){st.passesInRow=0;if(!actStrike(st,pn,r,c,r2,c2))return;advTurn(st);bc(room);if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>execAI(st,room),600);return;}
            if(type==='pass'){if(!se)return;if(hasStrikes(st.board,pn))return;actPass(st,pn);advTurn(st);bc(room);if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>execAI(st,room),600);return;}}});
    socket.on('disconnect',()=>{for(const rid of Object.keys(rooms))if(rid.startsWith('AI_')&&rooms[rid].p1===socket.id)delete rooms[rid];});
});

server.listen(process.env.PORT||3000,()=>console.log(`RANKS v0.6.2 on port ${process.env.PORT||3000}`));
