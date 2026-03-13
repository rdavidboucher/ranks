const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

const USERNAME = process.env.GAME_USERNAME;
const PASSWORD = process.env.GAME_PASSWORD;
app.use((req, res, next) => {
  if (!USERNAME) return next();
  const basic = (req.headers.authorization || '').split(' ')[1] || '';
  const [u, p] = Buffer.from(basic, 'base64').toString().split(':');
  if (u && p && u === USERNAME && p === PASSWORD) return next();
  res.set('WWW-Authenticate', 'Basic realm="RANKS"');
  res.status(401).send('Auth required.');
});
app.use(express.static('public'));

const N = 7;
const PA = 1;
const PB = 2;
const QUAL = 21;
const MIN_PATH = 7;
const SEARCH_LIMIT = 250000;

function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function makeSupply() {
  const t = [];
  for (let v = 1; v <= 6; v++) for (let i = 0; i < 4; i++) t.push(v);
  return shuffle(t);
}
function mkBoard() {
  return Array.from({ length: N }, () => Array.from({ length: N }, () => ({ owner: null, stack: [], faceUp: [] })));
}
function mkState(rid) {
  return {
    roomId: rid,
    board: mkBoard(),
    supplies: { [PA]: makeSupply(), [PB]: makeSupply() },
    currentPlayer: PA,
    phase: 'PIE_PLACE',
    passesInRow: 0,
    winner: null,
    winCondition: null,
    graveyard: [],
    ko: { [PA]: null, [PB]: null },
    lastMove: null,
    lastCaptures: [],
    piePos: null,
    peekDone: false,
    peekedCells: { [PA]: new Set(), [PB]: new Set() },
    isAiGame: false,
    humanPlayer: PA,
    gameLog: [],
    metadata: { rid, p1_id: null, p2_id: null, start: Date.now() }
  };
}

function inB(r, c) { return r >= 0 && r < N && c >= 0 && c < N; }
function orth(r, c) {
  const o = [];
  for (const [dr, dc] of [[-1,0],[1,0],[0,-1],[0,1]]) {
    const rr = r + dr, cc = c + dc;
    if (inB(rr, cc)) o.push([rr, cc]);
  }
  return o;
}
function mt(cl) { return cl.owner === null || cl.stack.length === 0; }
function fuScore(cl) {
  let s = 0;
  for (let i = 0; i < cl.stack.length; i++) if (cl.faceUp[i]) s += cl.stack[i];
  return s;
}
function occCells(b, p) {
  const out = [];
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (!mt(b[r][c]) && b[r][c].owner === p) out.push([r, c]);
  return out;
}
function emptyCells(b) {
  const out = [];
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (mt(b[r][c])) out.push([r, c]);
  return out;
}
function eAdj(b, p, r, c) {
  const out = [];
  for (const [rr, cc] of orth(r, c)) if (!mt(b[rr][cc]) && b[rr][cc].owner !== p) out.push([rr, cc]);
  return out;
}
function hasStrikes(b, p) {
  for (const [r, c] of occCells(b, p)) if (eAdj(b, p, r, c).length) return true;
  return false;
}
function cloneBoard(b) {
  return b.map(row => row.map(cl => ({ owner: cl.owner, stack: cl.stack.slice(), faceUp: cl.faceUp.slice() })));
}

// ---------- Path logic (v0.6.3 valuable path) ----------
function bestValuablePath(board, p) {
  const nodes = new Map();
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
    const cl = board[r][c];
    if (!mt(cl) && cl.owner === p) nodes.set(`${r},${c}`, { r, c, score: fuScore(cl) });
  }
  if (!nodes.size) return { score: 0, len: 0, path: null };

  const adj = {};
  for (const [k, info] of nodes) {
    adj[k] = orth(info.r, info.c)
      .map(([rr, cc]) => `${rr},${cc}`)
      .filter(nk => nodes.has(nk))
      .sort((a, b) => nodes.get(b).score - nodes.get(a).score);
  }

  let best = { score: 0, len: 0, path: null };
  let it = 0;
  for (const [startK, start] of nodes) {
    const stack = [{ cur: startK, seen: new Set([startK]), score: start.score, len: 1, path: [ [start.r, start.c] ] }];
    while (stack.length) {
      if (++it > SEARCH_LIMIT) return best;
      const st = stack.pop();
      const stQual = st.len >= MIN_PATH;
      const bestQual = best.len >= MIN_PATH;
      const better =
        (stQual && !bestQual) ||
        (stQual && bestQual && (st.score > best.score || (st.score === best.score && st.len > best.len))) ||
        (!stQual && !bestQual && (st.len > best.len || (st.len === best.len && st.score > best.score)));
      if (better) {
        best = { score: st.score, len: st.len, path: st.path.slice() };
      }
      for (const nx of adj[st.cur]) {
        if (st.seen.has(nx)) continue;
        const ni = nodes.get(nx);
        const ns = new Set(st.seen);
        ns.add(nx);
        const np = st.path.slice();
        np.push([ni.r, ni.c]);
        stack.push({ cur: nx, seen: ns, score: st.score + ni.score, len: st.len + 1, path: np });
      }
    }
  }
  return best;
}
function checkValuablePath(board, p) {
  const best = bestValuablePath(board, p);
  return { ok: best.len >= MIN_PATH && best.score >= QUAL, ...best };
}
function progressScore(board, p) {
  const best = bestValuablePath(board, p);
  return best.score + Math.min(best.len, MIN_PATH) * 2;
}

function checkExt(st) {
  for (const p of [PA, PB]) {
    if (occCells(st.board, p).length === 0 && st.supplies[p].length === 0) return p;
  }
  return null;
}
function endGame(st, winner, reason) {
  st.winner = winner;
  st.winCondition = reason;
  st.phase = 'GAME_OVER';
  const who = winner === null ? 'Draw' : `P${winner}`;
  st.gameLog.unshift(`GAME OVER: ${who} — ${reason}`);
}
function checkVic(st, attacker) {
  const a = checkValuablePath(st.board, PA);
  const b = checkValuablePath(st.board, PB);
  if (a.ok && b.ok) {
    endGame(st, attacker || st.currentPlayer, `Valuable Path (simultaneous). W:${a.score}/${a.len} B:${b.score}/${b.len}`);
    return true;
  }
  if (a.ok) { endGame(st, PA, `Valuable Path ${a.score}/${a.len}`); return true; }
  if (b.ok) { endGame(st, PB, `Valuable Path ${b.score}/${b.len}`); return true; }
  return false;
}
function totalFU(board, p) {
  let s = 0;
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) if (!mt(board[r][c]) && board[r][c].owner === p) s += fuScore(board[r][c]);
  return s;
}
function finalByPass(st) {
  const s1 = totalFU(st.board, PA), s2 = totalFU(st.board, PB);
  const t1 = occCells(st.board, PA).length, t2 = occCells(st.board, PB).length;
  if (s1 > s2) endGame(st, PA, `Mutual Attrition. W:${s1} tiles:${t1} vs B:${s2} tiles:${t2}`);
  else if (s2 > s1) endGame(st, PB, `Mutual Attrition. W:${s1} tiles:${t1} vs B:${s2} tiles:${t2}`);
  else if (t1 > t2) endGame(st, PA, `Mutual Attrition tiebreak. W:${s1} tiles:${t1} vs B:${s2} tiles:${t2}`);
  else if (t2 > t1) endGame(st, PB, `Mutual Attrition tiebreak. W:${s1} tiles:${t1} vs B:${s2} tiles:${t2}`);
  else endGame(st, null, `Mutual Attrition draw. W:${s1} tiles:${t1} vs B:${s2} tiles:${t2}`);
}

function resolveStrike(st, p, aR, aC, tR, tC) {
  const b = st.board;
  const e = p === PA ? PB : PA;
  const ac = b[aR][aC];
  ac.faceUp[0] = true;

  const atkK = new Set([`${aR},${aC}`]);
  for (const [rr, cc] of orth(aR, aC)) if (!mt(b[rr][cc]) && b[rr][cc].owner === p) atkK.add(`${rr},${cc}`);
  const defK = new Set([`${tR},${tC}`]);
  for (const [rr, cc] of orth(tR, tC)) if (!mt(b[rr][cc]) && b[rr][cc].owner === e) defK.add(`${rr},${cc}`);

  for (const k of [...atkK, ...defK]) {
    const [r, c] = k.split(',').map(Number);
    b[r][c].faceUp = [true];
  }

  let aS = 0, dS = 0;
  for (const k of atkK) { const [r, c] = k.split(',').map(Number); aS += b[r][c].stack[0]; }
  for (const k of defK) { const [r, c] = k.split(',').map(Number); dS += b[r][c].stack[0]; }

  st.gameLog.unshift(`P${p} strikes (${aR+1},${aC+1})->(${tR+1},${tC+1}): ATK ${aS} vs DEF ${dS}`);

  const cap = [];
  function capCell(r, c) {
    const cl = b[r][c];
    st.graveyard.push({ owner: cl.owner, value: cl.stack[0] });
    cap.push({ owner: cl.owner, r, c });
    cl.owner = null;
    cl.stack = [];
    cl.faceUp = [];
  }

  if (aS > dS) { capCell(tR, tC); st.gameLog.unshift(`  Defender captured at (${tR+1},${tC+1})`); }
  else if (dS > aS) { capCell(aR, aC); st.gameLog.unshift(`  Attacker captured at (${aR+1},${aC+1})`); }
  else { capCell(aR, aC); capCell(tR, tC); st.gameLog.unshift('  Tie: both captured'); }

  st.ko = { [PA]: null, [PB]: null };
  for (const cs of cap) st.ko[cs.owner] = { r: cs.r, c: cs.c };
  st.lastMove = { player: p, r: aR, c: aC };
  st.lastCaptures = cap.map(c => ({ r: c.r, c: c.c, owner: c.owner }));

  const ext = checkExt(st);
  if (ext !== null) {
    endGame(st, ext === PA ? PB : PA, 'Extermination');
    return;
  }
  checkVic(st, p);
}

function actDeploy(st, p, r, c) {
  if (st.supplies[p].length === 0) return false;
  if (!mt(st.board[r][c])) return false;
  if (st.ko[p] && st.ko[p].r === r && st.ko[p].c === c) return false;
  const v = st.supplies[p].shift();
  st.board[r][c] = { owner: p, stack: [v], faceUp: [false] };
  st.lastMove = { player: p, r, c };
  st.lastCaptures = [];
  st.ko = { [PA]: null, [PB]: null };
  st.gameLog.unshift(`P${p} deploys at (${r+1},${c+1})`);
  checkVic(st);
  return true;
}
function actStrike(st, p, aR, aC, tR, tC) {
  const a = st.board[aR][aC], t = st.board[tR][tC];
  if (mt(a) || a.owner !== p) return false;
  if (mt(t) || t.owner === p) return false;
  if (Math.abs(aR - tR) + Math.abs(aC - tC) !== 1) return false;
  resolveStrike(st, p, aR, aC, tR, tC);
  return true;
}
function actPass(st, p) {
  st.gameLog.unshift(`P${p} passes`);
  st.passesInRow++;
  st.ko = { [PA]: null, [PB]: null };
  if (st.passesInRow >= 2) finalByPass(st);
}
function advTurn(st) {
  if (st.phase === 'GAME_OVER') return;
  st.currentPlayer = st.currentPlayer === PA ? PB : PA;
  st.peekDone = false;
  st.phase = 'PEEK';
}

function stateView(st, viewer) {
  const bv = st.board.map(row => row.map(cl => {
    if (mt(cl)) return { owner: null, tiles: [] };
    return { owner: cl.owner, height: 1, tiles: [{ value: cl.faceUp[0] ? cl.stack[0] : null, faceUp: cl.faceUp[0], owner: cl.owner }] };
  }));
  const oppPeeked = [...(st.peekedCells[viewer === PA ? PB : PA] || [])];
  const q1 = bestValuablePath(st.board, PA).score;
  const q2 = bestValuablePath(st.board, PB).score;
  return {
    board: bv,
    supplies: { [PA]: st.supplies[PA].length, [PB]: st.supplies[PB].length },
    myNextDraw: st.supplies[viewer]?.[0] ?? null,
    currentPlayer: st.currentPlayer,
    phase: st.phase,
    winner: st.winner,
    winCondition: st.winCondition,
    graveyard: st.graveyard,
    ko: st.ko,
    lastMove: st.lastMove,
    lastCaptures: st.lastCaptures || [],
    peekDone: st.peekDone,
    passesInRow: st.passesInRow,
    gameLog: st.gameLog.slice(0, 60),
    isAiGame: st.isAiGame,
    qualThreshold: QUAL,
    qualMinLength: MIN_PATH,
    boardSize: N,
    qualScores: { [PA]: q1, [PB]: q2 },
    oppPeeked
  };
}

function bc(room) {
  const st = room.state;
  if (st.isAiGame) {
    if (room.p1 && room.p1 !== 'AI') io.to(room.p1).emit('update', stateView(st, st.humanPlayer));
    return;
  }
  if (room.p1 && room.p1 !== 'AI') io.to(room.p1).emit('update', stateView(st, PA));
  if (room.p2 && room.p2 !== 'AI') io.to(room.p2).emit('update', stateView(st, PB));
}

// ---------- AI ----------
function aiShouldSwap(v, r, c) {
  const center = (N - 1) / 2;
  const dist = Math.abs(r - center) + Math.abs(c - center);
  const own = v * 2 + (6 - dist);
  const opp = (7 - v) + dist;
  return own - opp > 4;
}
function legalStrikes(board, p) {
  const out = [];
  for (const [r, c] of occCells(board, p)) for (const [tr, tc] of eAdj(board, p, r, c)) out.push({ type: 'strike', atkR: r, atkC: c, tgtR: tr, tgtC: tc });
  return out;
}
function simState(st) {
  return {
    board: cloneBoard(st.board),
    supplies: { [PA]: st.supplies[PA].slice(), [PB]: st.supplies[PB].slice() },
    currentPlayer: st.currentPlayer,
    phase: st.phase,
    passesInRow: st.passesInRow,
    winner: null,
    winCondition: null,
    graveyard: st.graveyard.slice(),
    ko: { [PA]: st.ko[PA] ? { ...st.ko[PA] } : null, [PB]: st.ko[PB] ? { ...st.ko[PB] } : null },
    lastMove: st.lastMove ? { ...st.lastMove } : null,
    lastCaptures: []
  };
}
function applyMoveSim(st, p, mv) {
  const s = simState(st);
  s.currentPlayer = p;
  s.phase = 'ACTION';
  s.passesInRow = 0;
  if (mv.type === 'deploy') {
    if (!actDeploy(s, p, mv.r, mv.c)) return null;
  } else if (mv.type === 'strike') {
    if (!actStrike(s, p, mv.atkR, mv.atkC, mv.tgtR, mv.tgtC)) return null;
  } else if (mv.type === 'pass') {
    actPass(s, p);
  }
  return s;
}
function immediateWinningMoves(st, p) {
  const out = [];
  if (st.supplies[p].length > 0) {
    for (const [r, c] of emptyCells(st.board)) {
      if (st.ko[p] && st.ko[p].r === r && st.ko[p].c === c) continue;
      const sim = applyMoveSim(st, p, { type: 'deploy', r, c });
      if (sim && sim.winner === p) out.push({ type: 'deploy', r, c });
    }
  }
  for (const mv of legalStrikes(st.board, p)) {
    const sim = applyMoveSim(st, p, mv);
    if (sim && sim.winner === p) out.push(mv);
  }
  return out;
}
function opponentThreatInfo(st, me) {
  const opp = me === PA ? PB : PA;
  const immediate = immediateWinningMoves(st, opp);
  const best = bestValuablePath(st.board, opp);
  const near = immediate.length > 0 || (best.len >= MIN_PATH - 1 && best.score >= QUAL - 6);
  return { immediate, near, path: best.path || [], score: best.score, len: best.len };
}
function chooseBestStrikeOnPath(st, me, path) {
  if (!path || !path.length) return null;
  const pathSet = new Set(path.map(([r, c]) => `${r},${c}`));
  const candidates = legalStrikes(st.board, me).filter(mv => pathSet.has(`${mv.tgtR},${mv.tgtC}`));
  if (!candidates.length) return null;
  let best = candidates[0], bestSc = -1e9;
  for (const mv of candidates) {
    const sim = applyMoveSim(st, me, mv);
    if (!sim) continue;
    const opp = me === PA ? PB : PA;
    const myProg = progressScore(sim.board, me);
    const opProg = progressScore(sim.board, opp);
    const oppBest = bestValuablePath(sim.board, opp);
    const sc = myProg - opProg - oppBest.score * 3 - oppBest.len * 2;
    if (sc > bestSc) { bestSc = sc; best = mv; }
  }
  return best;
}
function aiMove(st) {
  const p = PB, e = PA;
  const hasS = st.supplies[p].length > 0;
  const strikes = legalStrikes(st.board, p);
  if (!hasS && !strikes.length) return { type: 'pass' };

  // 1) Win now.
  const wins = immediateWinningMoves(st, p);
  if (wins.length) return wins[0];

  // 2) Block opponent's immediate win.
  const oppWins = immediateWinningMoves(st, e);
  if (oppWins.length) {
    for (const mv of oppWins) {
      if (mv.type === 'deploy' && hasS) return { type: 'deploy', r: mv.r, c: mv.c };
    }
    const best = chooseBestStrikeOnPath(st, p, bestValuablePath(st.board, e).path);
    if (best) return best;
  }

  // 3) Emergency: opponent near a valuable path => strike the spine if possible.
  const threat = opponentThreatInfo(st, p);
  if (threat.near) {
    const strike = chooseBestStrikeOnPath(st, p, threat.path);
    if (strike) return strike;
    if (hasS && threat.path.length) {
      const pathSet = new Set(threat.path.map(([r, c]) => `${r},${c}`));
      const empties = emptyCells(st.board).filter(([r,c]) => !(st.ko[p] && st.ko[p].r === r && st.ko[p].c === c));
      let bestD = null, bestScore = -1e9;
      for (const [r,c] of empties) {
        let s = 0;
        for (const [rr,cc] of orth(r,c)) if (pathSet.has(`${rr},${cc}`)) s += 50;
        for (const [rr,cc] of orth(r,c)) if (!mt(st.board[rr][cc]) && st.board[rr][cc].owner === p) s += 10;
        if (s > bestScore) { bestScore = s; bestD = { type: 'deploy', r, c }; }
      }
      if (bestD) return bestD;
    }
  }

  // 4) General move search.
  const moves = [];
  if (hasS) {
    const empties = emptyCells(st.board).filter(([r,c]) => !(st.ko[p] && st.ko[p].r === r && st.ko[p].c === c));
    for (const [r,c] of empties) moves.push({ type: 'deploy', r, c });
  }
  moves.push(...strikes);
  if (!moves.length) return { type: 'pass' };

  let best = moves[0], bestSc = -1e9;
  for (const mv of moves) {
    const sim = applyMoveSim(st, p, mv);
    if (!sim) continue;
    if (sim.winner === p) return mv;
    const myBest = bestValuablePath(sim.board, p);
    const oppBest = bestValuablePath(sim.board, e);
    let sc = myBest.score * 4 + myBest.len * 7 - oppBest.score * 5 - oppBest.len * 8;
    sc += totalFU(sim.board, p) - totalFU(sim.board, e);
    sc += occCells(sim.board, p).length - occCells(sim.board, e).length;
    if (mv.type === 'strike') sc += 8;
    if (mv.type === 'deploy') {
      for (const [rr,cc] of orth(mv.r, mv.c)) if (!mt(st.board[rr][cc]) && st.board[rr][cc].owner === p) sc += 6;
      const center = (N - 1) / 2;
      sc += 4 - (Math.abs(mv.r - center) + Math.abs(mv.c - center));
    }
    if (sc > bestSc) { bestSc = sc; best = mv; }
  }
  return best;
}
function execAI(st, room) {
  if (st.currentPlayer !== PB || !st.isAiGame || st.phase === 'GAME_OVER') return;
  if (st.phase === 'PEEK') st.phase = 'ACTION';
  const mv = aiMove(st);
  if (mv.type === 'deploy') { st.passesInRow = 0; actDeploy(st, PB, mv.r, mv.c); }
  else if (mv.type === 'strike') { st.passesInRow = 0; actStrike(st, PB, mv.atkR, mv.atkC, mv.tgtR, mv.tgtC); }
  else actPass(st, PB);
  if (st.phase !== 'GAME_OVER') advTurn(st);
  bc(room);
}

const rooms = {};
io.on('connection', (socket) => {
  socket.on('joinGame', (irid) => {
    let rid = String(irid).toUpperCase().trim();
    const ai = rid === 'PLAYAI';
    if (ai) rid = `AI_${socket.id}`;

    if (!rooms[rid]) {
      const st = mkState(rid);
      st.isAiGame = ai;
      st.metadata.p1_id = socket.id;
      st.metadata.p2_id = ai ? 'AI' : null;
      rooms[rid] = { state: st, p1: socket.id, p2: ai ? 'AI' : null };
      socket.join(rid);
      socket.emit('init', { player: ai ? st.humanPlayer : PA, roomId: rid });
      if (ai) socket.emit('update', stateView(st, st.humanPlayer)); else socket.emit('waiting');
    } else if (rooms[rid].p2 === null) {
      rooms[rid].p2 = socket.id;
      rooms[rid].state.metadata.p2_id = socket.id;
      socket.join(rid);
      socket.emit('init', { player: PB, roomId: rid });
      io.to(rooms[rid].p1).emit('init', { player: PA, roomId: rid });
      bc(rooms[rid]);
    } else {
      socket.emit('roomFull');
    }
  });

  socket.on('rejoinGame', ({ roomId: rid, player: pl }) => {
    const room = rooms[rid];
    if (!room) return socket.emit('rejoinFailed', 'Not found');
    if (room.state.phase === 'GAME_OVER') return socket.emit('rejoinFailed', 'Over');
    if (room.state.isAiGame) {
      room.p1 = socket.id;
      room.state.metadata.p1_id = socket.id;
      socket.join(rid);
      socket.emit('init', { player: room.state.humanPlayer, roomId: rid });
      socket.emit('update', stateView(room.state, room.state.humanPlayer));
      return;
    }
    if (pl === PA) { room.p1 = socket.id; room.state.metadata.p1_id = socket.id; }
    else if (pl === PB && room.p2 !== 'AI') { room.p2 = socket.id; room.state.metadata.p2_id = socket.id; }
    else return socket.emit('rejoinFailed', 'Invalid');
    socket.join(rid);
    socket.emit('init', { player: pl, roomId: rid });
    socket.emit('update', stateView(room.state, pl));
  });

  socket.on('action', (data) => {
    const { roomId: rid, type, r, c, r2, c2, swap } = data;
    const room = rooms[rid];
    if (!room) return;
    const st = room.state;
    let pn = null;
    if (st.isAiGame) {
      if (socket.id === room.p1) pn = st.humanPlayer;
    } else {
      pn = socket.id === room.p1 ? PA : (socket.id === room.p2 ? PB : null);
    }
    if (pn === null) return;

    if (st.phase === 'PIE_PLACE' && pn === PA && type === 'place') {
      if (!mt(st.board[r][c])) return;
      const v = st.supplies[PA].shift();
      st.board[r][c] = { owner: PA, stack: [v], faceUp: [false] };
      st.piePos = { r, c };
      st.lastMove = { player: PA, r, c };
      st.phase = st.isAiGame ? 'PEEK' : 'PIE_DECISION';
      st.currentPlayer = PB;
      st.gameLog.unshift(`P1 opening at (${r+1},${c+1})`);
      if (st.isAiGame) {
        if (aiShouldSwap(v, r, c)) {
          st.humanPlayer = PB;
          st.currentPlayer = PB;
          st.gameLog.unshift('AI swaps: AI is White, human is Black.');
          io.to(room.p1).emit('init', { player: PB, roomId: rid });
          bc(room);
        } else {
          st.humanPlayer = PA;
          st.currentPlayer = PB;
          st.gameLog.unshift('AI continues as Black.');
          bc(room);
          setTimeout(() => execAI(st, room), 350);
        }
      } else {
        bc(room);
      }
      return;
    }

    if (st.phase === 'PIE_DECISION' && pn === PB && type === 'pieDecision') {
      if (swap) {
        [room.p1, room.p2] = [room.p2, room.p1];
        st.metadata.p1_id = room.p1;
        st.metadata.p2_id = room.p2;
        st.currentPlayer = PB;
        st.gameLog.unshift('P2 swapped.');
        io.to(room.p1).emit('init', { player: PA, roomId: rid });
        io.to(room.p2).emit('init', { player: PB, roomId: rid });
      } else {
        st.currentPlayer = PB;
        st.gameLog.unshift('No swap.');
      }
      st.phase = 'PEEK';
      bc(room);
      return;
    }

    if (st.phase === 'PEEK' && pn === st.currentPlayer) {
      if (type === 'peek') {
        const cl = st.board[r][c];
        if (!mt(cl) && cl.owner === pn) {
          socket.emit('peekResult', { r, c, values: cl.stack });
          st.peekedCells[pn].add(`${r},${c}`);
          st.gameLog.unshift(`P${pn} peeks at (${r+1},${c+1})`);
        }
      }
      if (type === 'skipPeek' || type === 'peek') {
        st.peekDone = true;
        st.phase = 'ACTION';
        bc(room);
      }
      return;
    }

    if (st.phase === 'ACTION' && pn === st.currentPlayer) {
      const supplyEmpty = st.supplies[pn].length === 0;
      if (type === 'deploy' && !supplyEmpty) {
        st.passesInRow = 0;
        if (!actDeploy(st, pn, r, c)) return;
        advTurn(st); bc(room);
        if (st.isAiGame && st.currentPlayer === PB && st.phase !== 'GAME_OVER') setTimeout(() => execAI(st, room), 350);
        return;
      }
      if (type === 'strike') {
        st.passesInRow = 0;
        if (!actStrike(st, pn, r, c, r2, c2)) return;
        advTurn(st); bc(room);
        if (st.isAiGame && st.currentPlayer === PB && st.phase !== 'GAME_OVER') setTimeout(() => execAI(st, room), 350);
        return;
      }
      if (type === 'pass') {
        if (!supplyEmpty) return;
        if (hasStrikes(st.board, pn)) return;
        actPass(st, pn);
        advTurn(st); bc(room);
        if (st.isAiGame && st.currentPlayer === PB && st.phase !== 'GAME_OVER') setTimeout(() => execAI(st, room), 350);
      }
    }
  });

  socket.on('disconnect', () => {
    for (const rid of Object.keys(rooms)) if (rid.startsWith('AI_') && rooms[rid].p1 === socket.id) delete rooms[rid];
  });
});

server.listen(process.env.PORT || 3000, () => console.log(`RANKS v0.6.3 (no stacks) on port ${process.env.PORT || 3000}`));
