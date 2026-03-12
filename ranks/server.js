const express    = require('express');
const app        = express();
const http       = require('http');
const server     = http.createServer(app);
const { Server } = require('socket.io');
const io         = new Server(server);

const USERNAME = process.env.GAME_USERNAME;
const PASSWORD = process.env.GAME_PASSWORD;

app.use((req, res, next) => {
    if (!USERNAME) return next();
    const b64auth = (req.headers.authorization || '').split(' ')[1] || '';
    const [login, password] = Buffer.from(b64auth, 'base64').toString().split(':');
    if (login && password && login === USERNAME && password === PASSWORD) return next();
    res.set('WWW-Authenticate', 'Basic realm="RANKS"');
    res.status(401).send('Authentication required.');
});
app.use(express.static('public'));

const N = 7, PA = 1, PB = 2, QUAL = 21;

function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}
function makeSupply(){const t=[];for(let v=1;v<=6;v++)for(let i=0;i<4;i++)t.push(v);return shuffle(t);}
function createBoard(){return Array.from({length:N},()=>Array.from({length:N},()=>({owner:null,stack:[],faceUp:[]})));}
function inB(r,c){return r>=0&&r<N&&c>=0&&c<N;}
function orth(r,c){const o=[];for(const[dr,dc]of[[-1,0],[1,0],[0,-1],[0,1]]){const rr=r+dr,cc=c+dc;if(inB(rr,cc))o.push([rr,cc]);}return o;}
function empty(cl){return cl.owner===null||cl.stack.length===0;}
function height(cl){return cl.stack.length;}
function faceUpScore(cl){let s=0;for(let i=0;i<cl.stack.length;i++)if(cl.faceUp[i])s+=cl.stack[i];return s;}

function createGameState(roomId){
    return{roomId,board:createBoard(),supplies:{[PA]:makeSupply(),[PB]:makeSupply()},
        currentPlayer:PA,phase:'PIE_PLACE',passesInRow:0,winner:null,winCondition:null,
        graveyard:[],ko:{[PA]:null,[PB]:null},lastMove:null,piePos:null,peekDone:false,
        isAiGame:false,gameLog:[],metadata:{roomId,p1_id:null,p2_id:null,startTime:Date.now()}};
}

function occupiedCells(b,p){const o=[];for(let r=0;r<N;r++)for(let c=0;c<N;c++)if(!empty(b[r][c])&&b[r][c].owner===p)o.push([r,c]);return o;}
function emptyCells(b){const o=[];for(let r=0;r<N;r++)for(let c=0;c<N;c++)if(empty(b[r][c]))o.push([r,c]);return o;}
function enemyAdj(b,p,r,c){const o=[];for(const[rr,cc]of orth(r,c))if(!empty(b[rr][cc])&&b[rr][cc].owner!==p)o.push([rr,cc]);return o;}
function legalStrikes(b,p){for(const[r,c]of occupiedCells(b,p))if(enemyAdj(b,p,r,c).length>0)return true;return false;}

// Qualification score: sum of face-up values for a player
function playerQualScore(b,p){
    let s=0;
    for(let r=0;r<N;r++)for(let c=0;c<N;c++){
        const cl=b[r][c];
        if(!empty(cl)&&cl.owner===p) s+=faceUpScore(cl);
    }
    return s;
}

// Qualified connection: simple path edge-to-edge with face-up score >= QUAL
function checkQualConn(b,p){
    const nodes=new Map();
    for(let r=0;r<N;r++)for(let c=0;c<N;c++){
        const cl=b[r][c];
        if(!empty(cl)&&cl.owner===p) nodes.set(`${r},${c}`,faceUpScore(cl));
    }
    if(!nodes.size)return false;
    const adj={};
    for(const k of nodes.keys()){
        const[r,c]=k.split(',').map(Number);
        adj[k]=[];
        for(const[rr,cc]of orth(r,c)){const nk=`${rr},${cc}`;if(nodes.has(nk))adj[k].push(nk);}
    }
    let it=0;
    function dfs(starts,goal){
        for(const s of starts){
            const stk=[{c:s,seen:new Set([s]),sc:nodes.get(s)}];
            while(stk.length){if(++it>500000)return false;const{c:cur,seen,sc}=stk.pop();
                if(goal(cur)&&sc>=QUAL)return true;
                for(const nx of(adj[cur]||[]))if(!seen.has(nx)){const ns=new Set(seen);ns.add(nx);stk.push({c:nx,seen:ns,sc:sc+nodes.get(nx)});}
            }
        }return false;
    }
    const rs=[];for(let c=0;c<N;c++)if(nodes.has(`0,${c}`))rs.push(`0,${c}`);
    if(rs.length&&dfs(rs,k=>k.split(',')[0]===String(N-1)))return true;
    const cs=[];for(let r=0;r<N;r++)if(nodes.has(`${r},0`))cs.push(`${r},0`);
    if(cs.length&&dfs(cs,k=>k.split(',')[1]===String(N-1)))return true;
    return false;
}

function checkExtermination(st){
    for(const p of[PA,PB])if(occupiedCells(st.board,p).length===0&&st.supplies[p].length===0)return p;
    return null;
}

function checkVictory(st,atkr){
    const c1=checkQualConn(st.board,PA),c2=checkQualConn(st.board,PB);
    if(c1&&c2){st.winner=atkr||st.currentPlayer;st.winCondition='Qualified Connection (simultaneous)';st.phase='GAME_OVER';return true;}
    if(c1){st.winner=PA;st.winCondition='Qualified Connection';st.phase='GAME_OVER';return true;}
    if(c2){st.winner=PB;st.winCondition='Qualified Connection';st.phase='GAME_OVER';return true;}
    return false;
}

// v0.6.2 scoring: sum all face-up tiles on board
function finalizeByPasses(st){
    const s1=playerQualScore(st.board,PA), s2=playerQualScore(st.board,PB);
    const t1=occupiedCells(st.board,PA).length, t2=occupiedCells(st.board,PB).length;
    st.phase='GAME_OVER';
    if(s1>s2)st.winner=PA;
    else if(s2>s1)st.winner=PB;
    else if(t1>t2)st.winner=PA;
    else if(t2>t1)st.winner=PB;
    else st.winner=null;
    st.winCondition=`Scoring (W:${s1} tiles:${t1} vs B:${s2} tiles:${t2})`;
}

// Combat
function resolveStrike(st,player,aR,aC,tR,tC){
    const b=st.board, enemy=player===PA?PB:PA, ac=b[aR][aC];
    ac.faceUp[ac.stack.length-1]=true; // reveal attacker's top

    const atkK=new Set([`${aR},${aC}`]);
    for(const[rr,cc]of orth(aR,aC))if(!empty(b[rr][cc])&&b[rr][cc].owner===player)atkK.add(`${rr},${cc}`);
    const defK=new Set([`${tR},${tC}`]);
    for(const[rr,cc]of orth(tR,tC))if(!empty(b[rr][cc])&&b[rr][cc].owner===enemy)defK.add(`${rr},${cc}`);

    for(const k of[...atkK,...defK]){const[r,c]=k.split(',').map(Number);b[r][c].faceUp=b[r][c].faceUp.map(()=>true);}

    let aS=0,dS=0;
    for(const k of atkK){const[r,c]=k.split(',').map(Number);aS+=b[r][c].stack.reduce((a,v)=>a+v,0);}
    for(const k of defK){const[r,c]=k.split(',').map(Number);dS+=b[r][c].stack.reduce((a,v)=>a+v,0);}

    st.gameLog.unshift(`P${player} strikes (${aR+1},${aC+1})->(${tR+1},${tC+1}): ATK ${aS} vs DEF ${dS}`);

    const cap=[];
    function capCell(r,c){const cl=b[r][c];for(const v of cl.stack)st.graveyard.push({owner:cl.owner,value:v});cap.push({owner:cl.owner,r,c});cl.stack=[];cl.faceUp=[];cl.owner=null;}

    if(aS>dS){capCell(tR,tC);st.gameLog.unshift(`  Defender captured at (${tR+1},${tC+1})`);}
    else if(dS>aS){capCell(aR,aC);st.gameLog.unshift(`  Attacker captured at (${aR+1},${aC+1})`);}
    else{capCell(aR,aC);capCell(tR,tC);st.gameLog.unshift(`  Tie: both captured`);}

    st.ko={[PA]:null,[PB]:null};
    for(const cs of cap)st.ko[cs.owner]={r:cs.r,c:cs.c};
    st.lastMove={player,r:aR,c:aC};

    const ext=checkExtermination(st);
    if(ext!==null){st.winner=ext===PA?PB:PA;st.winCondition='Extermination';st.phase='GAME_OVER';return;}
    checkVictory(st,player);
}

function actionDeploy(st,p,r,c){
    if(st.supplies[p].length===0)return false;
    if(!empty(st.board[r][c]))return false;
    if(st.ko[p]&&st.ko[p].r===r&&st.ko[p].c===c)return false;
    const v=st.supplies[p].shift();
    st.board[r][c]={owner:p,stack:[v],faceUp:[false]};
    st.lastMove={player:p,r,c};
    st.ko={[PA]:null,[PB]:null};
    st.gameLog.unshift(`P${p} deploys at (${r+1},${c+1})`);
    checkVictory(st);return true;
}
function actionReinforce(st,p,r,c){
    if(st.supplies[p].length===0)return false;
    const cl=st.board[r][c];
    if(empty(cl)||cl.owner!==p||height(cl)!==1)return false;
    const v=st.supplies[p].shift();
    cl.stack.push(v);cl.faceUp.push(false);
    st.lastMove={player:p,r,c};
    st.ko={[PA]:null,[PB]:null};
    st.gameLog.unshift(`P${p} reinforces at (${r+1},${c+1})`);
    checkVictory(st);return true;
}
function actionStrike(st,p,aR,aC,tR,tC){
    const a=st.board[aR][aC],t=st.board[tR][tC];
    if(empty(a)||a.owner!==p)return false;
    if(empty(t)||t.owner===p)return false;
    if(Math.abs(aR-tR)+Math.abs(aC-tC)!==1)return false;
    resolveStrike(st,p,aR,aC,tR,tC);return true;
}
function actionPass(st,p){
    st.gameLog.unshift(`P${p} passes`);st.passesInRow++;
    st.ko={[PA]:null,[PB]:null};
    if(st.passesInRow>=2)finalizeByPasses(st);
}
function advanceTurn(st){
    if(st.phase==='GAME_OVER')return;
    st.currentPlayer=st.currentPlayer===PA?PB:PA;
    st.peekDone=false;st.phase='PEEK';
}

// State view: NEVER reveal face-down values, even to owner
function stateView(st,viewer){
    const bv=st.board.map(row=>row.map(cl=>{
        if(empty(cl))return{owner:null,tiles:[]};
        return{owner:cl.owner,height:height(cl),
            tiles:cl.stack.map((v,i)=>({value:cl.faceUp[i]?v:null,faceUp:cl.faceUp[i],owner:cl.owner}))};
    }));
    return{board:bv,
        supplies:{[PA]:st.supplies[PA].length,[PB]:st.supplies[PB].length},
        myNextDraw:st.supplies[viewer]?.[0]??null,
        currentPlayer:st.currentPlayer,phase:st.phase,winner:st.winner,winCondition:st.winCondition,
        graveyard:st.graveyard,ko:st.ko,lastMove:st.lastMove,peekDone:st.peekDone,
        passesInRow:st.passesInRow,gameLog:st.gameLog.slice(0,50),isAiGame:st.isAiGame,
        qualThreshold:QUAL,boardSize:N,
        qualScores:{[PA]:playerQualScore(st.board,PA),[PB]:playerQualScore(st.board,PB)},
    };
}

function broadcastUpdate(room){
    const st=room.state;
    if(room.p1&&room.p1!=='AI')io.to(room.p1).emit('update',stateView(st,PA));
    if(room.p2&&room.p2!=='AI')io.to(room.p2).emit('update',stateView(st,PB));
}

// ═══ AI — connection-oriented ═══
function bfsReachable(b,p,starts){
    const seen=new Set(starts.map(([r,c])=>`${r},${c}`));
    const q=[...starts];
    while(q.length){const[r,c]=q.shift();for(const[rr,cc]of orth(r,c)){const k=`${rr},${cc}`;if(!seen.has(k)&&!empty(b[rr][cc])&&b[rr][cc].owner===p){seen.add(k);q.push([rr,cc]);}}}
    return seen;
}

function connProgress(b,p){
    // Measure best connection progress for both axes
    let best=0;
    // Row axis: row 0 -> row N-1
    const topCells=[];for(let c=0;c<N;c++)if(!empty(b[0][c])&&b[0][c].owner===p)topCells.push([0,c]);
    if(topCells.length){
        const reached=bfsReachable(b,p,topCells);
        let maxRow=0;for(const k of reached){const r=parseInt(k);if(r>maxRow)maxRow=r;}
        best=Math.max(best,maxRow/(N-1));
    }
    const botCells=[];for(let c=0;c<N;c++)if(!empty(b[N-1][c])&&b[N-1][c].owner===p)botCells.push([N-1,c]);
    if(botCells.length){
        const reached=bfsReachable(b,p,botCells);
        let minRow=N-1;for(const k of reached){const r=parseInt(k);if(r<minRow)minRow=r;}
        best=Math.max(best,(N-1-minRow)/(N-1));
    }
    // Col axis
    const leftCells=[];for(let r=0;r<N;r++)if(!empty(b[r][0])&&b[r][0].owner===p)leftCells.push([r,0]);
    if(leftCells.length){
        const reached=bfsReachable(b,p,leftCells);
        let maxCol=0;for(const k of reached){const c=parseInt(k.split(',')[1]);if(c>maxCol)maxCol=c;}
        best=Math.max(best,maxCol/(N-1));
    }
    const rightCells=[];for(let r=0;r<N;r++)if(!empty(b[r][N-1])&&b[r][N-1].owner===p)rightCells.push([r,N-1]);
    if(rightCells.length){
        const reached=bfsReachable(b,p,rightCells);
        let minCol=N-1;for(const k of reached){const c=parseInt(k.split(',')[1]);if(c<minCol)minCol=c;}
        best=Math.max(best,(N-1-minCol)/(N-1));
    }
    return best; // 0..1, 1 = fully connected
}

function aiBestAxis(b,p){
    // Determine which axis is most promising
    let bestAxis='row',bestProgress=-1;
    // Row: check from top
    const topStarts=[];for(let c=0;c<N;c++)if(!empty(b[0][c])&&b[0][c].owner===p)topStarts.push([0,c]);
    if(topStarts.length){const reached=bfsReachable(b,p,topStarts);let mx=0;for(const k of reached)mx=Math.max(mx,parseInt(k));if(mx>bestProgress){bestProgress=mx;bestAxis='row';}}
    // Col: check from left
    const leftStarts=[];for(let r=0;r<N;r++)if(!empty(b[r][0])&&b[r][0].owner===p)leftStarts.push([r,0]);
    if(leftStarts.length){const reached=bfsReachable(b,p,leftStarts);let mx=0;for(const k of reached)mx=Math.max(mx,parseInt(k.split(',')[1]));if(mx>bestProgress){bestProgress=mx;bestAxis='col';}}
    return{axis:bestAxis,progress:bestProgress};
}

function aiChooseMove(st){
    const b=st.board,p=PB,e=PA;
    const hasS=st.supplies[p].length>0;
    if(!hasS&&!legalStrikes(b,p))return{type:'pass'};
    if(!hasS)return aiBestStrike(b,p);

    const forbidden=st.ko[p];

    // Immediate win/block
    for(const[r,c]of emptyCells(b)){
        if(forbidden&&forbidden.r===r&&forbidden.c===c)continue;
        const sim=JSON.parse(JSON.stringify(b));
        sim[r][c]={owner:p,stack:[1],faceUp:[false]};
        if(checkQualConn(sim,p))return{type:'deploy',r,c};
    }
    for(const[r,c]of emptyCells(b)){
        if(forbidden&&forbidden.r===r&&forbidden.c===c)continue;
        const sim=JSON.parse(JSON.stringify(b));
        sim[r][c]={owner:e,stack:[1],faceUp:[false]};
        if(checkQualConn(sim,e))return{type:'deploy',r,c};
    }

    const myInfo=aiBestAxis(b,p);
    const ownSet=new Set(occupiedCells(b,p).map(([r,c])=>`${r},${c}`));
    const center=(N-1)/2;
    const moves=[];

    // Deploy: score by connection contribution
    for(const[r,c]of emptyCells(b)){
        if(forbidden&&forbidden.r===r&&forbidden.c===c)continue;
        let s=0;
        // Adjacency to own chain
        let adjOwn=0;
        for(const[rr,cc]of orth(r,c))if(ownSet.has(`${rr},${cc}`))adjOwn++;
        s+=adjOwn*12;

        // Connection direction bonus
        if(myInfo.axis==='row'){
            // Reward cells that advance toward far row, penalize lateral spread
            s+=(r===0||r===N-1)?8:0; // edge bonus
            // Prefer cells beyond current frontier
            if(r>myInfo.progress)s+=15;
            // Slight center column preference
            s+=3*(3-Math.abs(c-center));
        } else {
            s+=(c===0||c===N-1)?8:0;
            if(c>myInfo.progress)s+=15;
            s+=3*(3-Math.abs(r-center));
        }

        // Block enemy path: reward cells near enemy frontier
        const eInfo=aiBestAxis(b,e);
        if(eInfo.progress>=3){
            if(myInfo.axis==='row'&&eInfo.axis==='col')s+=Math.abs(c-eInfo.progress)<2?10:0;
            else if(myInfo.axis==='col'&&eInfo.axis==='row')s+=Math.abs(r-eInfo.progress)<2?10:0;
        }

        moves.push({type:'deploy',r,c,score:s});
    }

    // Reinforce
    for(const[r,c]of occupiedCells(b,p)){
        if(height(b[r][c])===1){
            let s=enemyAdj(b,p,r,c).length*18-4;
            moves.push({type:'reinforce',r,c,score:s});
        }
    }

    // Strike
    for(const[r,c]of occupiedCells(b,p)){
        for(const[tr,tc]of enemyAdj(b,p,r,c)){
            let aS=b[r][c].stack.reduce((a,v)=>a+v,0);
            for(const[rr,cc]of orth(r,c))if(!empty(b[rr][cc])&&b[rr][cc].owner===p)aS+=b[rr][cc].stack.reduce((a,v)=>a+v,0);
            let dS=b[tr][tc].stack.reduce((a,v)=>a+v,0);
            for(const[rr,cc]of orth(tr,tc))if(!empty(b[rr][cc])&&b[rr][cc].owner!==p)dS+=b[rr][cc].stack.reduce((a,v)=>a+v,0);
            let s=aS>dS?(aS-dS)*3+8:-(dS-aS)*4;
            // Bonus for striking enemy tiles that block our path
            if(myInfo.axis==='row'&&(tr===0||tr===N-1))s+=6;
            if(myInfo.axis==='col'&&(tc===0||tc===N-1))s+=6;
            moves.push({type:'strike',atkR:r,atkC:c,tgtR:tr,tgtC:tc,score:s});
        }
    }

    if(!moves.length)return{type:'pass'};
    moves.sort((a,b)=>b.score-a.score);
    return moves[0];
}

function aiBestStrike(b,p){
    const s=[];
    for(const[r,c]of occupiedCells(b,p))for(const[tr,tc]of enemyAdj(b,p,r,c))
        s.push({type:'strike',atkR:r,atkC:c,tgtR:tr,tgtC:tc,score:b[r][c].stack.reduce((a,v)=>a+v,0)});
    s.sort((a,b)=>b.score-a.score);
    return s[0]||{type:'pass'};
}

function executeAiTurn(st,room){
    if(st.currentPlayer!==PB||!st.isAiGame||st.phase==='GAME_OVER')return;
    if(st.phase==='PEEK')st.phase='ACTION';
    const mv=aiChooseMove(st);
    if(mv.type==='deploy'){st.passesInRow=0;actionDeploy(st,PB,mv.r,mv.c);}
    else if(mv.type==='reinforce'){st.passesInRow=0;actionReinforce(st,PB,mv.r,mv.c);}
    else if(mv.type==='strike'){st.passesInRow=0;actionStrike(st,PB,mv.atkR,mv.atkC,mv.tgtR,mv.tgtC);}
    else actionPass(st,PB);
    if(st.phase!=='GAME_OVER')advanceTurn(st);
    broadcastUpdate(room);
}

// ═══ ROOMS & SOCKETS ═══
const rooms={};
io.on('connection',(socket)=>{
    socket.on('joinGame',(inputRoomId)=>{
        let roomId=String(inputRoomId).toUpperCase().trim();
        const isAI=roomId==='PLAYAI';
        if(isAI)roomId=`AI_${socket.id}`;
        if(!rooms[roomId]){
            const st=createGameState(roomId);st.isAiGame=isAI;
            st.metadata.p1_id=socket.id;st.metadata.p2_id=isAI?'AI':null;
            rooms[roomId]={state:st,p1:socket.id,p2:isAI?'AI':null};
            socket.join(roomId);socket.emit('init',{player:PA,roomId});
            if(isAI)socket.emit('update',stateView(st,PA));
            else socket.emit('waiting');
        }else if(rooms[roomId].p2===null){
            rooms[roomId].p2=socket.id;rooms[roomId].state.metadata.p2_id=socket.id;
            socket.join(roomId);socket.emit('init',{player:PB,roomId});
            io.to(rooms[roomId].p1).emit('init',{player:PA,roomId});
            broadcastUpdate(rooms[roomId]);
        }else socket.emit('roomFull');
    });

    socket.on('rejoinGame',({roomId,player})=>{
        const room=rooms[roomId];if(!room){socket.emit('rejoinFailed','Room not found');return;}
        if(room.state.phase==='GAME_OVER'){socket.emit('rejoinFailed','Game over');return;}
        if(player===PA){room.p1=socket.id;room.state.metadata.p1_id=socket.id;}
        else if(player===PB&&room.p2!=='AI'){room.p2=socket.id;room.state.metadata.p2_id=socket.id;}
        else{socket.emit('rejoinFailed','Invalid');return;}
        socket.join(roomId);socket.emit('init',{player,roomId});
        socket.emit('update',stateView(room.state,player));
    });

    socket.on('action',(data)=>{
        const{roomId,type,r,c,r2,c2,swap}=data;
        const room=rooms[roomId];if(!room)return;
        const st=room.state;
        const pn=socket.id===room.p1?PA:(socket.id===room.p2?PB:null);
        if(pn===null)return;

        if(st.phase==='PIE_PLACE'&&pn===PA&&type==='place'){
            if(!empty(st.board[r][c]))return;
            const v=st.supplies[PA].shift();
            st.board[r][c]={owner:PA,stack:[v],faceUp:[false]};
            st.piePos={r,c};st.phase='PIE_DECISION';st.currentPlayer=PB;
            st.gameLog.unshift(`P1 opening tile at (${r+1},${c+1})`);
            if(st.isAiGame){
                st.gameLog.unshift('AI continues as Black.');
                st.phase='PEEK';st.currentPlayer=PB;
                broadcastUpdate(room);
                setTimeout(()=>executeAiTurn(st,room),600);
            }else broadcastUpdate(room);
            return;
        }

        if(st.phase==='PIE_DECISION'&&pn===PB&&type==='pieDecision'){
            if(swap){[room.p1,room.p2]=[room.p2,room.p1];st.metadata.p1_id=room.p1;st.metadata.p2_id=room.p2;
                st.currentPlayer=PB;st.gameLog.unshift('P2 swapped.');
                io.to(room.p1).emit('init',{player:PA,roomId});io.to(room.p2).emit('init',{player:PB,roomId});
            }else{st.currentPlayer=PB;st.gameLog.unshift('No swap. P2 plays next.');}
            st.phase='PEEK';broadcastUpdate(room);return;
        }

        if(st.phase==='PEEK'&&pn===st.currentPlayer){
            if(type==='peek'){
                const cl=st.board[r][c];
                if(!empty(cl)&&cl.owner===pn)
                    socket.emit('peekResult',{r,c,values:cl.stack});
            }
            if(type==='skipPeek'||type==='peek'){
                st.peekDone=true;st.phase='ACTION';broadcastUpdate(room);return;
            }
        }

        if(st.phase==='ACTION'&&pn===st.currentPlayer){
            const se=st.supplies[pn].length===0;
            if(type==='deploy'&&!se){st.passesInRow=0;if(!actionDeploy(st,pn,r,c))return;advanceTurn(st);broadcastUpdate(room);
                if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>executeAiTurn(st,room),600);return;}
            if(type==='reinforce'&&!se){st.passesInRow=0;if(!actionReinforce(st,pn,r,c))return;advanceTurn(st);broadcastUpdate(room);
                if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>executeAiTurn(st,room),600);return;}
            if(type==='strike'){st.passesInRow=0;if(!actionStrike(st,pn,r,c,r2,c2))return;advanceTurn(st);broadcastUpdate(room);
                if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>executeAiTurn(st,room),600);return;}
            if(type==='pass'){if(!se)return;if(legalStrikes(st.board,pn))return;actionPass(st,pn);advanceTurn(st);broadcastUpdate(room);
                if(st.isAiGame&&st.currentPlayer===PB&&st.phase!=='GAME_OVER')setTimeout(()=>executeAiTurn(st,room),600);return;}
        }
    });

    socket.on('disconnect',()=>{for(const rid of Object.keys(rooms))if(rid.startsWith('AI_')&&rooms[rid].p1===socket.id)delete rooms[rid];});
});

const PORT=process.env.PORT||3000;
server.listen(PORT,()=>console.log(`RANKS v0.6.2 on port ${PORT}`));
