const express    = require('express');
const app        = express();
const http       = require('http');
const server     = http.createServer(app);
const { Server } = require('socket.io');
const io         = new Server(server);
// const fetch    = require('node-fetch');
// const FormData = require('form-data');

// --- CONFIGURATION ---
const USERNAME = process.env.GAME_USERNAME;
const PASSWORD = process.env.GAME_PASSWORD;
// const DISCORD_WEBHOOK_URL = process.env.DISCORD_WEBHOOK_URL;

// --- AUTH MIDDLEWARE ---
app.use((req, res, next) => {
    const b64auth = (req.headers.authorization || '').split(' ')[1] || '';
    const [login, password] = Buffer.from(b64auth, 'base64').toString().split(':');
    if (login && password && login === USERNAME && password === PASSWORD) return next();
    res.set('WWW-Authenticate', 'Basic realm="RANKS"');
    res.status(401).send('Authentication required to access RANKS.');
});

app.use(express.static('public'));

// --- DISCORD WEBHOOK (COMMENTED OUT) ---
/*
function sendLogToDiscord(log) {
    if (!DISCORD_WEBHOOK_URL) return;
    const p1 = log.p1_id === 'AI' ? 'AI' : 'Human';
    const p2 = log.p2_id === 'AI' ? 'AI' : 'Human';
    const winner = log.winner === 1 ? 'Player 1 (White/N-S)' : log.winner === 2 ? 'Player 2 (Black/E-W)' : 'Draw';
    const content = `**RANKS GAME REPORT**\n**Room:** \`${log.roomId}\`\n**Mode:** ${p1} vs ${p2}\n**Winner:** ${winner}\n**Condition:** ${log.winCondition}\n**Turns:** ${log.turns}\n**Duration:** ${Math.round(log.durationSeconds)}s`;
    const form = new FormData();
    form.append('payload_json', JSON.stringify({ content }));
    form.append('file', Buffer.from(JSON.stringify(log, null, 2), 'utf-8'), `ranks_${log.roomId}.json`);
    fetch(DISCORD_WEBHOOK_URL, { method: 'POST', body: form })
        .then(r => console.log('Discord status:', r.status))
        .catch(e => console.error('Discord error:', e));
}
*/

// --- CONSTANTS ---
const BOARD_SIZE = 9;
const PA = 1;  // White — connects Row 1 to Row 9 (North-South)
const PB = 2;  // Black — connects Col 1 to Col 9 (East-West)

// --- HELPERS ---
function shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
}

function makeSupply(owner) {
    const tiles = [];
    for (let v = 1; v <= 6; v++) {
        for (let i = 0; i < 4; i++) tiles.push({ owner, value: v, faceUp: false });
    }
    return shuffle(tiles);
}

function createBoard() {
    return Array.from({ length: BOARD_SIZE }, () =>
        Array.from({ length: BOARD_SIZE }, () => ({ tiles: [] }))
    );
}

function cellOwner(cell) {
    return cell.tiles.length > 0 ? cell.tiles[cell.tiles.length - 1].owner : null;
}

function cellTop(cell) {
    return cell.tiles.length > 0 ? cell.tiles[cell.tiles.length - 1] : null;
}

function cellValue(cell) {
    return cell.tiles.reduce((s, t) => s + t.value, 0);
}

function inBounds(r, c) {
    return r >= 0 && r < BOARD_SIZE && c >= 0 && c < BOARD_SIZE;
}

function neighbors(r, c) {
    const out = [];
    for (let dr = -1; dr <= 1; dr++) {
        for (let dc = -1; dc <= 1; dc++) {
            if (dr === 0 && dc === 0) continue;
            if (inBounds(r + dr, c + dc)) out.push([r + dr, c + dc]);
        }
    }
    return out;
}

function manhattan(r1, c1, r2, c2) {
    return Math.abs(r1 - r2) + Math.abs(c1 - c2);
}

function getCluster(board, r, c, owner) {
    if (cellOwner(board[r][c]) !== owner) return [];
    const visited = new Set([`${r},${c}`]);
    const queue = [[r, c]];
    while (queue.length) {
        const [cr, cc] = queue.shift();
        for (const [nr, nc] of neighbors(cr, cc)) {
            const k = `${nr},${nc}`;
            if (!visited.has(k) && cellOwner(board[nr][nc]) === owner) {
                visited.add(k); queue.push([nr, nc]);
            }
        }
    }
    return [...visited].map(k => k.split(',').map(Number));
}

function hasPath(board, player) {
    const starts = [];
    if (player === PA) {
        for (let c = 0; c < BOARD_SIZE; c++) if (cellOwner(board[0][c]) === player) starts.push([0, c]);
    } else {
        for (let r = 0; r < BOARD_SIZE; r++) if (cellOwner(board[r][0]) === player) starts.push([r, 0]);
    }
    const visited = new Set();
    const queue = [];
    for (const s of starts) { const k = `${s[0]},${s[1]}`; if (!visited.has(k)) { visited.add(k); queue.push(s); } }
    while (queue.length) {
        const [r, c] = queue.shift();
        if ((player === PA && r === BOARD_SIZE - 1) || (player === PB && c === BOARD_SIZE - 1)) return true;
        for (const [nr, nc] of neighbors(r, c)) {
            const k = `${nr},${nc}`;
            if (!visited.has(k) && cellOwner(board[nr][nc]) === player) { visited.add(k); queue.push([nr, nc]); }
        }
    }
    return false;
}

function getValidMoves(board, player) {
    const placementSet = new Map();
    const stacks = [];
    const homeRow = player === PA ? 0 : null;
    const homeCol = player === PB ? 0 : null;

    if (homeRow !== null) {
        for (let c = 0; c < BOARD_SIZE; c++) {
            if (board[homeRow][c].tiles.length === 0) placementSet.set(`${homeRow},${c}`, [homeRow, c]);
        }
    }
    if (homeCol !== null) {
        for (let r = 0; r < BOARD_SIZE; r++) {
            if (board[r][homeCol].tiles.length === 0) placementSet.set(`${r},${homeCol}`, [r, homeCol]);
        }
    }
    for (let r = 0; r < BOARD_SIZE; r++) {
        for (let c = 0; c < BOARD_SIZE; c++) {
            if (cellOwner(board[r][c]) === player) {
                for (const [nr, nc] of neighbors(r, c)) {
                    if (board[nr][nc].tiles.length === 0) placementSet.set(`${nr},${nc}`, [nr, nc]);
                }
                if (board[r][c].tiles.length === 1) stacks.push([r, c]);
            }
        }
    }
    return { placements: [...placementSet.values()], stacks };
}

// --- COMBAT ---
function resolveCombat(board, trigR, trigC, attacker, defender) {
    const atkCluster = getCluster(board, trigR, trigC, attacker);
    const defSeedSet = new Map();
    for (const [nr, nc] of neighbors(trigR, trigC)) {
        if (cellOwner(board[nr][nc]) === defender) {
            for (const pos of getCluster(board, nr, nc, defender)) {
                defSeedSet.set(`${pos[0]},${pos[1]}`, pos);
            }
        }
    }
    const defCluster = [...defSeedSet.values()];
    if (defCluster.length === 0) return null;

    for (const [r, c] of atkCluster) for (const t of board[r][c].tiles) t.faceUp = true;
    for (const [r, c] of defCluster) for (const t of board[r][c].tiles) t.faceUp = true;

    const atkPower = atkCluster.reduce((s, [r, c]) => s + cellValue(board[r][c]), 0);
    const defPower = defCluster.reduce((s, [r, c]) => s + cellValue(board[r][c]), 0);

    if (atkPower === defPower) return { tie: true, atkPower, defPower, atkCluster, defCluster, destroyed: [] };

    const winner  = atkPower > defPower ? attacker : defender;
    const loser   = winner === attacker ? defender : attacker;
    const damage  = Math.abs(atkPower - defPower);
    const sorted  = (loser === defender ? defCluster : atkCluster)
        .slice()
        .sort((a, b) => manhattan(a[0], a[1], trigR, trigC) - manhattan(b[0], b[1], trigR, trigC));

    let remaining = damage;
    const destroyed = [];
    for (const [r, c] of sorted) {
        if (remaining <= 0) break;
        while (board[r][c].tiles.length > 0 && remaining > 0) {
            const tile = board[r][c].tiles.pop();
            destroyed.push({ r, c, tile });
            remaining -= tile.value;
        }
    }
    return { tie: false, winner, loser, atkPower, defPower, damage, atkCluster, defCluster, destroyed };
}

// --- AI ---
function aiChooseMove(board, supplies, player, aiKnown) {
    const enemy = player === PA ? PB : PA;
    const { placements, stacks } = getValidMoves(board, player);
    if (!placements.length && !stacks.length) return null;

    // Check immediate win first
    for (const [r, c] of placements) {
        const sim = board.map(row => row.map(cell => ({ tiles: cell.tiles.map(t => ({ ...t })) })));
        sim[r][c].tiles.push({ owner: player, value: 3, faceUp: false });
        if (hasPath(sim, player)) return { action: 'place', r, c };
    }

    let best = null, bestScore = -Infinity;
    const allMoves = [
        ...placements.map(([r, c]) => ({ action: 'place', r, c })),
        ...stacks.map(([r, c]) => ({ action: 'stack', r, c }))
    ];

    for (const move of allMoves) {
        let score = 0;
        const { r, c } = move;

        // Path progress
        const distNear = player === PA ? r : c;
        const distFar  = BOARD_SIZE - 1 - distNear;
        score += (BOARD_SIZE - 1 - Math.floor((distNear + distFar) / 2)) * 5;

        // Connectivity
        const ownNbrs = neighbors(r, c).filter(([nr, nc]) => cellOwner(board[nr][nc]) === player);
        score += ownNbrs.length * 8;

        // Enemy proximity — estimate combat outcome
        const enemyNbrs = neighbors(r, c).filter(([nr, nc]) => cellOwner(board[nr][nc]) === enemy);
        if (enemyNbrs.length > 0) {
            let ownPower = ownNbrs.reduce((s, [nr, nc]) => {
                return s + getCluster(board, nr, nc, player)
                    .reduce((ss, [cr, cc]) => ss + cellValue(board[cr][cc]), 0);
            }, 3);
            let enemyPower = 0;
            const seen = new Set();
            for (const [nr, nc] of enemyNbrs) {
                for (const [cr, cc] of getCluster(board, nr, nc, enemy)) {
                    const k = `${cr},${cc}`;
                    if (!seen.has(k)) {
                        seen.add(k);
                        for (const t of board[cr][cc].tiles) {
                            enemyPower += t.faceUp ? t.value : (aiKnown[k] || 3.5);
                        }
                    }
                }
            }
            score += (ownPower - enemyPower) * 10;
        }

        // Stack near enemies
        if (move.action === 'stack') score += enemyNbrs.length * 6;

        // Penalise revealing a large cluster
        if (ownNbrs.length > 0) {
            const cluster = getCluster(board, ownNbrs[0][0], ownNbrs[0][1], player);
            const fdCount = cluster.reduce((s, [cr, cc]) =>
                s + board[cr][cc].tiles.filter(t => !t.faceUp).length, 0);
            score -= fdCount * 2;
        }

        if (score > bestScore) { bestScore = score; best = move; }
    }
    return best;
}

function aiChooseReveal(board, cluster, player) {
    const alive = cluster.filter(([r, c]) => cellOwner(board[r][c]) === player);
    const faceDown = alive
        .map(([r, c]) => ({ r, c, v: cellTop(board[r][c])?.value }))
        .filter(({ r, c }) => cellTop(board[r][c]) && !cellTop(board[r][c]).faceUp);
    if (!faceDown.length) return null;
    faceDown.sort((a, b) => a.v - b.v);
    return [faceDown[0].r, faceDown[0].c];
}

function aiChooseRecon(board, enemy) {
    const candidates = [];
    for (let r = 0; r < BOARD_SIZE; r++) {
        for (let c = 0; c < BOARD_SIZE; c++) {
            const top = cellTop(board[r][c]);
            if (top && top.owner === enemy && !top.faceUp) {
                candidates.push([r, c, enemy === PA ? r : c]);
            }
        }
    }
    if (!candidates.length) return null;
    candidates.sort((a, b) => b[2] - a[2]);
    return [candidates[0][0], candidates[0][1]];
}

// --- GAME STATE ---
function createGameState(roomId) {
    return {
        roomId,
        board:         createBoard(),
        supplies:      { [PA]: makeSupply(PA), [PB]: makeSupply(PB) },
        currentPlayer: PA,
        phase:         'PIE_PLACE',   // PIE_PLACE | PIE_DECISION | MAIN | REVEAL_RULE | RECON | GAME_OVER
        piePos:        null,
        revealCluster: [],
        revealPlayer:  null,
        pendingCombat: null,
        reconWinner:   null,
        reconEnemy:    null,
        turnNumber:    0,
        winner:        null,
        winCondition:  null,
        isAiGame:      false,
        aiKnown:       {},
        gameLog:       [],
        lastCombat:    null,
        metadata: { startTime: Date.now(), endTime: null, durationSeconds: 0, p1_id: null, p2_id: null }
    };
}

// Player-specific view: hides opponent face-down tile values
function stateView(state, playerNum) {
    const opp    = playerNum === PA ? PB : PA;
    const supply = JSON.parse(JSON.stringify(state.supplies));
    // Scrub opponent supply values
    for (const t of supply[opp]) t.value = null;

    const board = state.board.map(row =>
        row.map(cell => ({
            tiles: cell.tiles.map(t => ({
                owner:  t.owner,
                value:  (!t.faceUp && t.owner === opp) ? null : t.value,
                faceUp: t.faceUp
            }))
        }))
    );

    return {
        board,
        supplies:      { [PA]: supply[PA].length, [PB]: supply[PB].length },
        currentPlayer: state.currentPlayer,
        phase:         state.phase,
        piePos:        state.piePos,
        revealCluster: state.revealCluster,
        revealPlayer:  state.revealPlayer,
        reconWinner:   state.reconWinner,
        reconEnemy:    state.reconEnemy,
        turnNumber:    state.turnNumber,
        winner:        state.winner,
        winCondition:  state.winCondition,
        lastCombat:    state.lastCombat,
        gameLog:       state.gameLog.slice(0, 8)
    };
}

function broadcastUpdate(room, io) {
    const s = room.state;
    if (room.p1) io.to(room.p1).emit('update', stateView(s, PA));
    if (room.p2 && room.p2 !== 'AI') io.to(room.p2).emit('update', stateView(s, PB));
}

// --- TURN LOGIC ---
function advanceTurn(state) {
    if (hasPath(state.board, PA)) { endGame(state, PA, 'path'); return; }
    if (hasPath(state.board, PB)) { endGame(state, PB, 'path'); return; }

    if (state.supplies[PA].length === 0 && state.supplies[PB].length === 0) {
        let scoreA = 0, scoreB = 0;
        for (let r = 0; r < BOARD_SIZE; r++) {
            for (let c = 0; c < BOARD_SIZE; c++) {
                const o = cellOwner(state.board[r][c]);
                if (o === PA) scoreA += cellValue(state.board[r][c]);
                else if (o === PB) scoreB += cellValue(state.board[r][c]);
            }
        }
        if (scoreA > scoreB) endGame(state, PA, 'attrition');
        else if (scoreB > scoreA) endGame(state, PB, 'attrition');
        else endGame(state, null, 'draw');
        return;
    }

    state.currentPlayer = state.currentPlayer === PA ? PB : PA;
    state.turnNumber++;
    state.phase        = 'MAIN';
    state.revealCluster = [];
    state.revealPlayer  = null;
    state.pendingCombat = null;
    state.reconWinner   = null;
    state.reconEnemy    = null;
    state.lastCombat    = null;
}

function endGame(state, winner, condition) {
    state.winner       = winner;
    state.winCondition = condition;
    state.phase        = 'GAME_OVER';
    state.metadata.endTime        = Date.now();
    state.metadata.durationSeconds = (state.metadata.endTime - state.metadata.startTime) / 1000;
    state.gameLog.unshift(`GAME OVER: ${winner ? `P${winner} wins by ${condition}` : 'Draw'}`);
}

function startRecon(state, room, combatResult) {
    if (!combatResult || combatResult.tie) { advanceTurn(state); return; }
    const winner = combatResult.winner;
    const enemy  = winner === PA ? PB : PA;

    // Check for face-down targets
    let hasFD = false;
    for (let r = 0; r < BOARD_SIZE && !hasFD; r++) {
        for (let c = 0; c < BOARD_SIZE && !hasFD; c++) {
            const top = cellTop(state.board[r][c]);
            if (top && top.owner === enemy && !top.faceUp) hasFD = true;
        }
    }
    const hasSupply = state.supplies[enemy].length > 0;

    if (!hasFD && !hasSupply) { advanceTurn(state); return; }

    if (!hasFD) {
        // Supply peek (auto-send to winner)
        const val = state.supplies[enemy][0].value;
        const winnerSocket = winner === PA ? room.p1 : room.p2;
        if (winnerSocket && winnerSocket !== 'AI') {
            io.to(winnerSocket).emit('peekResult', { r: -1, c: -1, value: val, fromSupply: true });
        } else {
            state.aiKnown[`supply_${enemy}`] = val;
        }
        state.gameLog.unshift(`P${winner} peeked at P${enemy}'s supply`);
        advanceTurn(state);
        return;
    }

    if (state.isAiGame && winner === PB) {
        const pos = aiChooseRecon(state.board, enemy);
        if (pos) {
            const top = cellTop(state.board[pos[0]][pos[1]]);
            if (top) state.aiKnown[`${pos[0]},${pos[1]}`] = top.value;
            state.gameLog.unshift(`AI peeked at (${pos[0]+1},${pos[1]+1})`);
        }
        advanceTurn(state);
        return;
    }

    state.phase      = 'RECON';
    state.reconWinner = winner;
    state.reconEnemy  = enemy;
}

function executePlacement(state, room, r, c, isStack) {
    const player  = state.currentPlayer;
    const supply  = state.supplies[player];
    if (supply.length === 0) return;

    const tile = supply.shift();
    tile.faceUp = false;
    state.board[r][c].tiles.push(tile);

    state.gameLog.unshift(`P${player} ${isStack ? 'stacked' : 'placed'} at (${r+1},${c+1})`);

    const enemy = player === PA ? PB : PA;

    // Capture reveal cluster BEFORE combat
    const ownNbrs = neighbors(r, c).filter(([nr, nc]) => cellOwner(state.board[nr][nc]) === player);
    const revealCluster = ownNbrs.length > 0 ? getCluster(state.board, r, c, player) : [];

    // Resolve combat if adjacent to enemy
    const enemyNbrs = neighbors(r, c).filter(([nr, nc]) => cellOwner(state.board[nr][nc]) === enemy);
    let combat = null;
    if (enemyNbrs.length > 0) {
        combat = resolveCombat(state.board, r, c, player, enemy);
        state.lastCombat = combat ? {
            tie:      combat.tie,
            winner:   combat.tie ? null : combat.winner,
            atkPower: combat.atkPower,
            defPower: combat.defPower,
            damage:   combat.tie ? 0 : combat.damage,
            destroyed: (combat.destroyed || []).map(d => ({ r: d.r, c: d.c, owner: d.tile.owner, value: d.tile.value }))
        } : null;
        if (combat && !combat.tie) {
            state.gameLog.unshift(`COMBAT: P${combat.winner} wins (${combat.atkPower} vs ${combat.defPower}, dmg ${combat.damage})`);
            for (const d of combat.destroyed) {
                state.gameLog.unshift(`  Destroyed P${d.tile.owner} [${d.tile.value}] at (${d.r+1},${d.c+1})`);
            }
        } else if (combat && combat.tie) {
            state.gameLog.unshift(`COMBAT TIE (${combat.atkPower} vs ${combat.defPower})`);
        }
    }

    // Alive cluster post-combat (some tiles may have been destroyed)
    const aliveCluster = revealCluster.filter(([cr, cc]) => cellOwner(state.board[cr][cc]) === player);
    const needsReveal  = aliveCluster.some(([cr, cc]) => {
        const top = cellTop(state.board[cr][cc]);
        return top && !top.faceUp;
    });

    if (state.isAiGame) {
        // Auto-handle reveal and recon for AI turns or when AI is opponent
        if (needsReveal) {
            const pos = aiChooseReveal(state.board, aliveCluster, player);
            if (pos) {
                const top = cellTop(state.board[pos[0]][pos[1]]);
                if (top) { top.faceUp = true; state.gameLog.unshift(`P${player} reveals [${top.value}] at (${pos[0]+1},${pos[1]+1})`); }
            }
        }
        startRecon(state, room, combat);
    } else {
        // PvP — interactive phases
        if (needsReveal) {
            state.phase         = 'REVEAL_RULE';
            state.revealCluster = aliveCluster;
            state.revealPlayer  = player;
            state.pendingCombat = combat;
        } else if (combat && !combat.tie) {
            startRecon(state, room, combat);
        } else {
            advanceTurn(state);
        }
    }
}

function executeAiTurn(state, room) {
    if (state.currentPlayer !== PB || !state.isAiGame) return;
    const { placements, stacks } = getValidMoves(state.board, PB);
    if (!placements.length && !stacks.length) { advanceTurn(state); broadcastUpdate(room, io); return; }

    const move = aiChooseMove(state.board, state.supplies, PB, state.aiKnown);
    if (!move) { advanceTurn(state); broadcastUpdate(room, io); return; }

    executePlacement(state, room, move.r, move.c, move.action === 'stack');
    broadcastUpdate(room, io);

    // If still AI's turn (e.g. after a phase that auto-resolved), keep going
    if (state.phase === 'MAIN' && state.currentPlayer === PB) {
        setTimeout(() => { executeAiTurn(state, room); }, 400);
    }
}

// --- ROOMS ---
const rooms = {};

io.on('connection', (socket) => {
    socket.on('joinGame', (inputRoomId) => {
        let roomId = String(inputRoomId).toUpperCase().trim();
        const isAI = roomId === 'PLAYAI';
        if (isAI) roomId = `AI_${socket.id}`;

        if (!rooms[roomId]) {
            const state = createGameState(roomId);
            state.isAiGame     = isAI;
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
            broadcastUpdate(rooms[roomId], io);
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
        const { roomId, type, r, c, swap } = data;
        const room = rooms[roomId];
        if (!room) return;
        const state = room.state;
        const playerNum = socket.id === room.p1 ? PA : (socket.id === room.p2 ? PB : null);
        if (playerNum === null) return;

        // PIE_PLACE: P1 places opening tile in row 0
        if (state.phase === 'PIE_PLACE' && playerNum === PA && type === 'place') {
            if (r !== 0 || state.board[r][c].tiles.length > 0) return;
            const tile = state.supplies[PA].shift();
            tile.faceUp = false;
            state.board[r][c].tiles.push(tile);
            state.piePos = { r, c };
            state.phase  = 'PIE_DECISION';
            state.currentPlayer = PB;
            state.gameLog.unshift(`P1 opening tile at (${r+1},${c+1})`);
            // AI auto-decides: always continue (no swap) for simplicity
            if (state.isAiGame) {
                state.gameLog.unshift('AI declines swap. P2 (AI) plays next.');
                state.phase         = 'MAIN';
                state.currentPlayer = PB;
                broadcastUpdate(room, io);
                setTimeout(() => { executeAiTurn(state, room); broadcastUpdate(room, io); }, 800);
            } else {
                broadcastUpdate(room, io);
            }
            return;
        }

        // PIE_DECISION: P2 swaps or continues (PvP only)
        if (state.phase === 'PIE_DECISION' && playerNum === PB && type === 'pieDecision') {
            if (swap) {
                // Swap socket assignments and supply ownership
                [room.p1, room.p2]    = [room.p2, room.p1];
                state.metadata.p1_id  = room.p1;
                state.metadata.p2_id  = room.p2;
                // Tile on board stays as owner:PA (N-S player, now room.p1 / original PB socket)
                state.currentPlayer   = PB;  // new PB (original PA socket) plays next
                state.gameLog.unshift('P2 swapped. Takes N-S. P1 (E-W) plays next.');
                io.to(room.p1).emit('init', { player: PA, roomId });
                io.to(room.p2).emit('init', { player: PB, roomId });
            } else {
                state.currentPlayer = PB;
                state.gameLog.unshift('No swap. P2 plays next.');
            }
            state.phase = 'MAIN';
            broadcastUpdate(room, io);
            return;
        }

        // MAIN: place or stack
        if (state.phase === 'MAIN' && playerNum === state.currentPlayer && (type === 'place' || type === 'stack')) {
            const { placements, stacks } = getValidMoves(state.board, playerNum);
            const valid = type === 'place'
                ? placements.some(([vr, vc]) => vr === r && vc === c)
                : stacks.some(([vr, vc]) => vr === r && vc === c);
            if (!valid) return;
            executePlacement(state, room, r, c, type === 'stack');
            broadcastUpdate(room, io);
            if (state.isAiGame && state.phase === 'MAIN' && state.currentPlayer === PB) {
                setTimeout(() => { executeAiTurn(state, room); broadcastUpdate(room, io); }, 700);
            }
            return;
        }

        // REVEAL_RULE: current player picks a face-down tile to flip
        if (state.phase === 'REVEAL_RULE' && playerNum === state.revealPlayer && type === 'reveal') {
            const inCluster = state.revealCluster.some(([cr, cc]) => cr === r && cc === c);
            const top = cellTop(state.board[r][c]);
            if (!inCluster || !top || top.faceUp || top.owner !== playerNum) return;
            top.faceUp = true;
            state.gameLog.unshift(`P${playerNum} reveals [${top.value}] at (${r+1},${c+1})`);
            const combat = state.pendingCombat;
            if (combat && !combat.tie) startRecon(state, room, combat);
            else advanceTurn(state);
            broadcastUpdate(room, io);
            if (state.isAiGame && state.phase === 'MAIN' && state.currentPlayer === PB) {
                setTimeout(() => { executeAiTurn(state, room); broadcastUpdate(room, io); }, 700);
            }
            return;
        }

        // RECON: winner peeks at one enemy face-down tile
        if (state.phase === 'RECON' && playerNum === state.reconWinner && type === 'recon') {
            const top = cellTop(state.board[r][c]);
            if (!top || top.owner !== state.reconEnemy || top.faceUp) return;
            socket.emit('peekResult', { r, c, value: top.value, fromSupply: false });
            state.gameLog.unshift(`P${playerNum} peeked at (${r+1},${c+1})`);
            advanceTurn(state);
            broadcastUpdate(room, io);
            if (state.isAiGame && state.phase === 'MAIN' && state.currentPlayer === PB) {
                setTimeout(() => { executeAiTurn(state, room); broadcastUpdate(room, io); }, 700);
            }
            return;
        }
    });

    socket.on('disconnect', () => {
        for (const rid of Object.keys(rooms)) {
            if (rid.startsWith('AI_') && rooms[rid].p1 === socket.id) delete rooms[rid];
        }
    });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`RANKS server running on port ${PORT}`));
