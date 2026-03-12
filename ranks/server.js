const express    = require('express');
const app        = express();
const http       = require('http');
const server     = http.createServer(app);
const { Server } = require('socket.io');
const io         = new Server(server);

const USERNAME = process.env.GAME_USERNAME;
const PASSWORD = process.env.GAME_PASSWORD;

app.use((req, res, next) => {
    const b64auth = (req.headers.authorization || '').split(' ')[1] || '';
    const [login, password] = Buffer.from(b64auth, 'base64').toString().split(':');
    if (login && password && login === USERNAME && password === PASSWORD) return next();
    res.set('WWW-Authenticate', 'Basic realm="RANKS"');
    res.status(401).send('Authentication required to access RANKS.');
});

app.use(express.static('public'));

// ═══ CONSTANTS ═══
const N = 7;
const PA = 1;
const PB = 2;
const QUAL_THRESHOLD = 21;

// ═══ HELPERS ═══
function shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
}

function makeSupply() {
    const tiles = [];
    for (let v = 1; v <= 6; v++)
        for (let i = 0; i < 4; i++) tiles.push(v);
    return shuffle(tiles);
}

function createBoard() {
    return Array.from({ length: N }, () =>
        Array.from({ length: N }, () => ({ owner: null, stack: [], faceUp: [] }))
    );
}

function inBounds(r, c) { return r >= 0 && r < N && c >= 0 && c < N; }

function orthNeighbors(r, c) {
    const out = [];
    for (const [dr, dc] of [[-1,0],[1,0],[0,-1],[0,1]]) {
        const rr = r+dr, cc = c+dc;
        if (inBounds(rr, cc)) out.push([rr, cc]);
    }
    return out;
}

function cellEmpty(cell) { return cell.owner === null || cell.stack.length === 0; }
function cellHeight(cell) { return cell.stack.length; }
function cellFaceUpScore(cell) {
    let s = 0;
    for (let i = 0; i < cell.stack.length; i++)
        if (cell.faceUp[i]) s += cell.stack[i];
    return s;
}

// ═══ GAME STATE ═══
function createGameState(roomId) {
    return {
        roomId,
        board: createBoard(),
        supplies: { [PA]: makeSupply(), [PB]: makeSupply() },
        currentPlayer: PA,
        phase: 'PIE_PLACE',
        passesInRow: 0,
        winner: null,
        winCondition: null,
        graveyard: [],
        ko: { [PA]: null, [PB]: null },
        lastMove: null,
        piePos: null,
        peekDone: false,
        isAiGame: false,
        gameLog: [],
        metadata: { roomId, p1_id: null, p2_id: null, startTime: Date.now() },
    };
}

// ═══ CELL QUERIES ═══
function occupiedCells(board, player) {
    const out = [];
    for (let r = 0; r < N; r++)
        for (let c = 0; c < N; c++)
            if (!cellEmpty(board[r][c]) && board[r][c].owner === player)
                out.push([r, c]);
    return out;
}

function emptyCells(board) {
    const out = [];
    for (let r = 0; r < N; r++)
        for (let c = 0; c < N; c++)
            if (cellEmpty(board[r][c])) out.push([r, c]);
    return out;
}

function enemyAdjacentTargets(board, player, r, c) {
    const out = [];
    for (const [rr, cc] of orthNeighbors(r, c))
        if (!cellEmpty(board[rr][cc]) && board[rr][cc].owner !== player)
            out.push([rr, cc]);
    return out;
}

function legalStrikesExist(board, player) {
    for (const [r, c] of occupiedCells(board, player))
        if (enemyAdjacentTargets(board, player, r, c).length > 0) return true;
    return false;
}

// ═══ QUALIFIED CONNECTION ═══
function checkQualifiedConnection(board, player) {
    const nodes = new Map();
    for (let r = 0; r < N; r++)
        for (let c = 0; c < N; c++) {
            const cell = board[r][c];
            if (!cellEmpty(cell) && cell.owner === player)
                nodes.set(`${r},${c}`, cellFaceUpScore(cell));
        }
    if (nodes.size === 0) return false;

    const adj = {};
    for (const key of nodes.keys()) {
        const [r, c] = key.split(',').map(Number);
        adj[key] = [];
        for (const [rr, cc] of orthNeighbors(r, c)) {
            const nk = `${rr},${cc}`;
            if (nodes.has(nk)) adj[key].push(nk);
        }
    }

    let iters = 0;
    function dfs(starts, goalTest) {
        for (const s of starts) {
            const stack = [{ cur: s, seen: new Set([s]), score: nodes.get(s) }];
            while (stack.length) {
                if (++iters > 500000) return false;
                const { cur, seen, score } = stack.pop();
                if (goalTest(cur) && score >= QUAL_THRESHOLD) return true;
                for (const nxt of (adj[cur] || [])) {
                    if (!seen.has(nxt)) {
                        const ns = new Set(seen); ns.add(nxt);
                        stack.push({ cur: nxt, seen: ns, score: score + nodes.get(nxt) });
                    }
                }
            }
        }
        return false;
    }

    const rowStarts = [];
    for (let c = 0; c < N; c++) if (nodes.has(`0,${c}`)) rowStarts.push(`0,${c}`);
    if (rowStarts.length && dfs(rowStarts, k => k.split(',')[0] === String(N-1))) return true;

    const colStarts = [];
    for (let r = 0; r < N; r++) if (nodes.has(`${r},0`)) colStarts.push(`${r},0`);
    if (colStarts.length && dfs(colStarts, k => k.split(',')[1] === String(N-1))) return true;

    return false;
}

// ═══ VICTORY ═══
function checkExtermination(state) {
    for (const p of [PA, PB])
        if (occupiedCells(state.board, p).length === 0 && state.supplies[p].length === 0) return p;
    return null;
}

function checkVictory(state, attackerForSimul) {
    const c1 = checkQualifiedConnection(state.board, PA);
    const c2 = checkQualifiedConnection(state.board, PB);
    if (c1 && c2) {
        state.winner = attackerForSimul || state.currentPlayer;
        state.winCondition = 'Qualified Connection (simultaneous)';
        state.phase = 'GAME_OVER'; return true;
    }
    if (c1) { state.winner = PA; state.winCondition = 'Qualified Connection'; state.phase = 'GAME_OVER'; return true; }
    if (c2) { state.winner = PB; state.winCondition = 'Qualified Connection'; state.phase = 'GAME_OVER'; return true; }
    return false;
}

// ═══ SCORING ═══
function bestPathScore(board, player) {
    const nodes = occupiedCells(board, player);
    if (!nodes.length) return { score: 0, len: 0 };
    const nodeSet = new Set(nodes.map(([r,c]) => `${r},${c}`));
    const weights = {};
    const adj = {};
    for (const [r,c] of nodes) {
        const k = `${r},${c}`;
        weights[k] = cellFaceUpScore(board[r][c]);
        adj[k] = [];
        for (const [rr,cc] of orthNeighbors(r,c))
            if (nodeSet.has(`${rr},${cc}`)) adj[k].push(`${rr},${cc}`);
    }
    let best = 0, bestLen = 0, iters = 0;
    for (const [sr,sc] of nodes) {
        const sk = `${sr},${sc}`;
        const stack = [{ cur: sk, seen: new Set([sk]), sc: weights[sk], ln: 1 }];
        while (stack.length) {
            if (++iters > 500000) break;
            const { cur, seen, sc, ln } = stack.pop();
            if (sc >= 1 && (sc > best || (sc === best && ln > bestLen))) { best = sc; bestLen = ln; }
            for (const nxt of adj[cur]) {
                if (!seen.has(nxt)) {
                    const ns = new Set(seen); ns.add(nxt);
                    stack.push({ cur: nxt, seen: ns, sc: sc + weights[nxt], ln: ln + 1 });
                }
            }
        }
        if (iters > 500000) break;
    }
    return { score: best, len: bestLen };
}

function finalizeByPasses(state) {
    const s1 = bestPathScore(state.board, PA);
    const s2 = bestPathScore(state.board, PB);
    state.phase = 'GAME_OVER';
    if (s1.score > s2.score) state.winner = PA;
    else if (s2.score > s1.score) state.winner = PB;
    else if (s1.len > s2.len) state.winner = PA;
    else if (s2.len > s1.len) state.winner = PB;
    else state.winner = null;
    state.winCondition = `Scoring (W: ${s1.score}/${s1.len} vs B: ${s2.score}/${s2.len})`;
}

// ═══ COMBAT ═══
function resolveStrike(state, player, atkR, atkC, tgtR, tgtC) {
    const board = state.board;
    const enemy = player === PA ? PB : PA;
    const aCell = board[atkR][atkC];

    // Reveal attacker's top
    if (aCell.stack.length >= 1) aCell.faceUp[aCell.stack.length - 1] = true;

    // Build clusters
    const atkKeys = new Set([`${atkR},${atkC}`]);
    for (const [rr,cc] of orthNeighbors(atkR, atkC))
        if (!cellEmpty(board[rr][cc]) && board[rr][cc].owner === player) atkKeys.add(`${rr},${cc}`);
    const defKeys = new Set([`${tgtR},${tgtC}`]);
    for (const [rr,cc] of orthNeighbors(tgtR, tgtC))
        if (!cellEmpty(board[rr][cc]) && board[rr][cc].owner === enemy) defKeys.add(`${rr},${cc}`);

    // Reveal all
    for (const key of [...atkKeys, ...defKeys]) {
        const [r,c] = key.split(',').map(Number);
        board[r][c].faceUp = board[r][c].faceUp.map(() => true);
    }

    // Sum
    let atkSum = 0, defSum = 0;
    for (const key of atkKeys) { const [r,c] = key.split(',').map(Number); atkSum += board[r][c].stack.reduce((s,v) => s+v, 0); }
    for (const key of defKeys) { const [r,c] = key.split(',').map(Number); defSum += board[r][c].stack.reduce((s,v) => s+v, 0); }

    state.gameLog.unshift(`P${player} strikes (${atkR+1},${atkC+1})->(${tgtR+1},${tgtC+1}): ATK ${atkSum} vs DEF ${defSum}`);

    const captured = [];
    function captureCell(r, c) {
        const cell = board[r][c];
        for (const v of cell.stack) state.graveyard.push({ owner: cell.owner, value: v });
        captured.push({ owner: cell.owner, r, c });
        cell.stack = []; cell.faceUp = []; cell.owner = null;
    }

    if (atkSum > defSum) {
        captureCell(tgtR, tgtC);
        state.gameLog.unshift(`  Defender captured at (${tgtR+1},${tgtC+1})`);
    } else if (defSum > atkSum) {
        captureCell(atkR, atkC);
        state.gameLog.unshift(`  Attacker captured at (${atkR+1},${atkC+1})`);
    } else {
        captureCell(atkR, atkC); captureCell(tgtR, tgtC);
        state.gameLog.unshift(`  Tie: both captured`);
    }

    state.ko = { [PA]: null, [PB]: null };
    for (const cs of captured) state.ko[cs.owner] = { r: cs.r, c: cs.c };
    state.lastMove = { player, r: atkR, c: atkC };

    const ext = checkExtermination(state);
    if (ext !== null) {
        state.winner = ext === PA ? PB : PA;
        state.winCondition = 'Extermination';
        state.phase = 'GAME_OVER';
        return;
    }
    checkVictory(state, player);
}

// ═══ ACTIONS ═══
function actionDeploy(state, player, r, c) {
    if (state.supplies[player].length === 0) return false;
    if (!cellEmpty(state.board[r][c])) return false;
    if (state.ko[player] && state.ko[player].r === r && state.ko[player].c === c) return false;
    const v = state.supplies[player].shift();
    state.board[r][c] = { owner: player, stack: [v], faceUp: [false] };
    state.lastMove = { player, r, c };
    state.ko = { [PA]: null, [PB]: null };
    state.gameLog.unshift(`P${player} deploys at (${r+1},${c+1})`);
    checkVictory(state);
    return true;
}

function actionReinforce(state, player, r, c) {
    if (state.supplies[player].length === 0) return false;
    const cell = state.board[r][c];
    if (cellEmpty(cell) || cell.owner !== player || cellHeight(cell) !== 1) return false;
    const v = state.supplies[player].shift();
    cell.stack.push(v);
    cell.faceUp.push(false);
    state.lastMove = { player, r, c };
    state.ko = { [PA]: null, [PB]: null };
    state.gameLog.unshift(`P${player} reinforces at (${r+1},${c+1})`);
    checkVictory(state);
    return true;
}

function actionStrike(state, player, atkR, atkC, tgtR, tgtC) {
    const a = state.board[atkR][atkC], t = state.board[tgtR][tgtC];
    if (cellEmpty(a) || a.owner !== player) return false;
    if (cellEmpty(t) || t.owner === player) return false;
    if (Math.abs(atkR-tgtR) + Math.abs(atkC-tgtC) !== 1) return false;
    resolveStrike(state, player, atkR, atkC, tgtR, tgtC);
    return true;
}

function actionPass(state, player) {
    state.gameLog.unshift(`P${player} passes`);
    state.passesInRow++;
    state.ko = { [PA]: null, [PB]: null };
    if (state.passesInRow >= 2) finalizeByPasses(state);
}

// ═══ TURN FLOW ═══
function advanceTurn(state) {
    if (state.phase === 'GAME_OVER') return;
    state.currentPlayer = state.currentPlayer === PA ? PB : PA;
    state.peekDone = false;
    state.phase = 'PEEK';
}

// ═══ STATE VIEW ═══
function stateView(state, viewer) {
    const boardView = state.board.map(row =>
        row.map(cell => {
            if (cellEmpty(cell)) return { owner: null, tiles: [] };
            return {
                owner: cell.owner,
                height: cellHeight(cell),
                tiles: cell.stack.map((v, i) => ({
                    value: (cell.faceUp[i] || cell.owner === viewer) ? v : null,
                    faceUp: cell.faceUp[i],
                    owner: cell.owner,
                })),
            };
        })
    );
    return {
        board: boardView,
        supplies: { [PA]: state.supplies[PA].length, [PB]: state.supplies[PB].length },
        myNextDraw: state.supplies[viewer]?.[0] ?? null,
        currentPlayer: state.currentPlayer,
        phase: state.phase,
        winner: state.winner,
        winCondition: state.winCondition,
        graveyard: state.graveyard,
        ko: state.ko,
        lastMove: state.lastMove,
        peekDone: state.peekDone,
        passesInRow: state.passesInRow,
        gameLog: state.gameLog.slice(0, 40),
        isAiGame: state.isAiGame,
        qualThreshold: QUAL_THRESHOLD,
        boardSize: N,
    };
}

function broadcastUpdate(room) {
    const state = room.state;
    if (room.p1 && room.p1 !== 'AI') io.to(room.p1).emit('update', stateView(state, PA));
    if (room.p2 && room.p2 !== 'AI') io.to(room.p2).emit('update', stateView(state, PB));
}

// ═══ AI ═══
function aiChooseMove(state) {
    const board = state.board, player = PB, enemy = PA;
    const hasSupply = state.supplies[player].length > 0;
    if (!hasSupply && !legalStrikesExist(board, player)) return { type: 'pass' };
    if (!hasSupply) return aiBestStrike(board, player);

    const forbidden = state.ko[player];

    // Immediate win
    for (const [r,c] of emptyCells(board)) {
        if (forbidden && forbidden.r === r && forbidden.c === c) continue;
        const sim = JSON.parse(JSON.stringify(board));
        sim[r][c] = { owner: player, stack: [1], faceUp: [false] };
        if (checkQualifiedConnection(sim, player)) return { type: 'deploy', r, c };
    }
    // Block
    for (const [r,c] of emptyCells(board)) {
        if (forbidden && forbidden.r === r && forbidden.c === c) continue;
        const sim = JSON.parse(JSON.stringify(board));
        sim[r][c] = { owner: enemy, stack: [1], faceUp: [false] };
        if (checkQualifiedConnection(sim, enemy)) return { type: 'deploy', r, c };
    }

    const moves = [];
    const ownSet = new Set(occupiedCells(board, player).map(([r,c]) => `${r},${c}`));
    const center = (N-1)/2;

    for (const [r,c] of emptyCells(board)) {
        if (forbidden && forbidden.r === r && forbidden.c === c) continue;
        let s = 0;
        for (const [rr,cc] of orthNeighbors(r,c)) if (ownSet.has(`${rr},${cc}`)) s += 10;
        s += 3*(6 - (Math.abs(r-center) + Math.abs(c-center)));
        if (r===0||r===N-1||c===0||c===N-1) s += 5;
        moves.push({ type: 'deploy', r, c, score: s });
    }

    for (const [r,c] of occupiedCells(board, player)) {
        if (cellHeight(board[r][c]) === 1) {
            let s = enemyAdjacentTargets(board, player, r, c).length * 15;
            moves.push({ type: 'reinforce', r, c, score: s });
        }
    }

    for (const [r,c] of occupiedCells(board, player)) {
        for (const [tr,tc] of enemyAdjacentTargets(board, player, r, c)) {
            let atkS = board[r][c].stack.reduce((a,v)=>a+v,0);
            for (const [rr,cc] of orthNeighbors(r,c))
                if (!cellEmpty(board[rr][cc]) && board[rr][cc].owner === player) atkS += board[rr][cc].stack.reduce((a,v)=>a+v,0);
            let defS = board[tr][tc].stack.reduce((a,v)=>a+v,0);
            for (const [rr,cc] of orthNeighbors(tr,tc))
                if (!cellEmpty(board[rr][cc]) && board[rr][cc].owner !== player) defS += board[rr][cc].stack.reduce((a,v)=>a+v,0);
            let s = atkS > defS ? (atkS-defS)*3 + 5 : -(defS-atkS)*4;
            moves.push({ type: 'strike', atkR: r, atkC: c, tgtR: tr, tgtC: tc, score: s });
        }
    }

    if (!moves.length) return { type: 'pass' };
    moves.sort((a,b) => b.score - a.score);
    return moves[0];
}

function aiBestStrike(board, player) {
    const strikes = [];
    for (const [r,c] of occupiedCells(board, player))
        for (const [tr,tc] of enemyAdjacentTargets(board, player, r, c)) {
            let s = board[r][c].stack.reduce((a,v)=>a+v,0);
            strikes.push({ type: 'strike', atkR: r, atkC: c, tgtR: tr, tgtC: tc, score: s });
        }
    strikes.sort((a,b) => b.score - a.score);
    return strikes[0] || { type: 'pass' };
}

function executeAiTurn(state, room) {
    if (state.currentPlayer !== PB || !state.isAiGame || state.phase === 'GAME_OVER') return;
    if (state.phase === 'PEEK') state.phase = 'ACTION';

    const move = aiChooseMove(state);
    if (move.type === 'deploy') { state.passesInRow = 0; actionDeploy(state, PB, move.r, move.c); }
    else if (move.type === 'reinforce') { state.passesInRow = 0; actionReinforce(state, PB, move.r, move.c); }
    else if (move.type === 'strike') { state.passesInRow = 0; actionStrike(state, PB, move.atkR, move.atkC, move.tgtR, move.tgtC); }
    else actionPass(state, PB);

    if (state.phase !== 'GAME_OVER') advanceTurn(state);
    broadcastUpdate(room);
}

// ═══ ROOMS ═══
const rooms = {};

io.on('connection', (socket) => {
    socket.on('joinGame', (inputRoomId) => {
        let roomId = String(inputRoomId).toUpperCase().trim();
        const isAI = roomId === 'PLAYAI';
        if (isAI) roomId = `AI_${socket.id}`;

        if (!rooms[roomId]) {
            const state = createGameState(roomId);
            state.isAiGame = isAI;
            state.metadata.p1_id = socket.id;
            state.metadata.p2_id = isAI ? 'AI' : null;
            rooms[roomId] = { state, p1: socket.id, p2: isAI ? 'AI' : null };
            socket.join(roomId);
            socket.emit('init', { player: PA, roomId });
            if (isAI) socket.emit('update', stateView(state, PA));
            else socket.emit('waiting');
        } else if (rooms[roomId].p2 === null) {
            rooms[roomId].p2 = socket.id;
            rooms[roomId].state.metadata.p2_id = socket.id;
            socket.join(roomId);
            socket.emit('init', { player: PB, roomId });
            io.to(rooms[roomId].p1).emit('init', { player: PA, roomId });
            broadcastUpdate(rooms[roomId]);
        } else {
            socket.emit('roomFull');
        }
    });

    socket.on('rejoinGame', ({ roomId, player }) => {
        const room = rooms[roomId];
        if (!room) { socket.emit('rejoinFailed', 'Room not found'); return; }
        if (room.state.phase === 'GAME_OVER') { socket.emit('rejoinFailed', 'Game already over'); return; }
        if (player === PA) { room.p1 = socket.id; room.state.metadata.p1_id = socket.id; }
        else if (player === PB && room.p2 !== 'AI') { room.p2 = socket.id; room.state.metadata.p2_id = socket.id; }
        else { socket.emit('rejoinFailed', 'Invalid seat'); return; }
        socket.join(roomId);
        socket.emit('init', { player, roomId });
        socket.emit('update', stateView(room.state, player));
    });

    socket.on('action', (data) => {
        const { roomId, type, r, c, r2, c2, swap } = data;
        const room = rooms[roomId];
        if (!room) return;
        const state = room.state;
        const playerNum = socket.id === room.p1 ? PA : (socket.id === room.p2 ? PB : null);
        if (playerNum === null) return;

        if (state.phase === 'PIE_PLACE' && playerNum === PA && type === 'place') {
            if (!cellEmpty(state.board[r][c])) return;
            const v = state.supplies[PA].shift();
            state.board[r][c] = { owner: PA, stack: [v], faceUp: [false] };
            state.piePos = { r, c };
            state.phase = 'PIE_DECISION';
            state.currentPlayer = PB;
            state.gameLog.unshift(`P1 opening tile at (${r+1},${c+1})`);
            if (state.isAiGame) {
                state.gameLog.unshift('AI continues as Black.');
                state.phase = 'PEEK';
                state.currentPlayer = PB;
                broadcastUpdate(room);
                setTimeout(() => executeAiTurn(state, room), 600);
            } else {
                broadcastUpdate(room);
            }
            return;
        }

        if (state.phase === 'PIE_DECISION' && playerNum === PB && type === 'pieDecision') {
            if (swap) {
                [room.p1, room.p2] = [room.p2, room.p1];
                state.metadata.p1_id = room.p1;
                state.metadata.p2_id = room.p2;
                state.currentPlayer = PB;
                state.gameLog.unshift('P2 swapped.');
                io.to(room.p1).emit('init', { player: PA, roomId });
                io.to(room.p2).emit('init', { player: PB, roomId });
            } else {
                state.currentPlayer = PB;
                state.gameLog.unshift('No swap. P2 plays next.');
            }
            state.phase = 'PEEK';
            broadcastUpdate(room);
            return;
        }

        if (state.phase === 'PEEK' && playerNum === state.currentPlayer) {
            if (type === 'peek') {
                const cell = state.board[r][c];
                if (!cellEmpty(cell) && cell.owner === playerNum) {
                    socket.emit('peekResult', { r, c, values: cell.stack });
                    state.gameLog.unshift(`P${playerNum} peeks at (${r+1},${c+1})`);
                }
            }
            if (type === 'skipPeek' || type === 'peek') {
                state.peekDone = true;
                state.phase = 'ACTION';
                broadcastUpdate(room);
                return;
            }
        }

        if (state.phase === 'ACTION' && playerNum === state.currentPlayer) {
            const supplyEmpty = state.supplies[playerNum].length === 0;

            if (type === 'deploy' && !supplyEmpty) {
                state.passesInRow = 0;
                if (!actionDeploy(state, playerNum, r, c)) return;
                advanceTurn(state); broadcastUpdate(room);
                if (state.isAiGame && state.currentPlayer === PB && state.phase !== 'GAME_OVER')
                    setTimeout(() => executeAiTurn(state, room), 600);
                return;
            }
            if (type === 'reinforce' && !supplyEmpty) {
                state.passesInRow = 0;
                if (!actionReinforce(state, playerNum, r, c)) return;
                advanceTurn(state); broadcastUpdate(room);
                if (state.isAiGame && state.currentPlayer === PB && state.phase !== 'GAME_OVER')
                    setTimeout(() => executeAiTurn(state, room), 600);
                return;
            }
            if (type === 'strike') {
                state.passesInRow = 0;
                if (!actionStrike(state, playerNum, r, c, r2, c2)) return;
                advanceTurn(state); broadcastUpdate(room);
                if (state.isAiGame && state.currentPlayer === PB && state.phase !== 'GAME_OVER')
                    setTimeout(() => executeAiTurn(state, room), 600);
                return;
            }
            if (type === 'pass') {
                if (!supplyEmpty) return;
                if (legalStrikesExist(state.board, playerNum)) return;
                actionPass(state, playerNum);
                advanceTurn(state); broadcastUpdate(room);
                if (state.isAiGame && state.currentPlayer === PB && state.phase !== 'GAME_OVER')
                    setTimeout(() => executeAiTurn(state, room), 600);
                return;
            }
        }
    });

    socket.on('disconnect', () => {
        for (const rid of Object.keys(rooms))
            if (rid.startsWith('AI_') && rooms[rid].p1 === socket.id) delete rooms[rid];
    });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`RANKS v0.6.1 server on port ${PORT}`));
