'use strict';
// 능력 대전 아레나 - 서버 (외부 패키지 없이 동작: 내장 WebSocket 구현)
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const W = 1000, H = 600;          // 경기장 크기
const PR = 18;                    // 플레이어 반지름
const BASE_SPEED = 230;
const MAX_HP = 100;
const MAX_PLAYERS = 4;
const WIN_ROUNDS = 3;             // 3라운드 선승

// ---------- 능력 정의 (클라이언트에도 전달) ----------
const SKILLS = {
  fireball: { name: '화염구', icon: '🔥', cd: 3000, desc: '폭발하는 불덩이. 직격 28 + 주변 14' },
  nova:     { name: '서리 폭발', icon: '❄️', cd: 6000, desc: '주변 적에게 10 피해 + 2.5초 둔화' },
  bolt:     { name: '번개', icon: '⚡', cd: 4000, desc: '벽까지 닿는 즉발 광선 26 피해' },
  blink:    { name: '순간이동', icon: '🌀', cd: 4000, desc: '조준 방향으로 순간 이동' },
  shield:   { name: '방어막', icon: '🛡️', cd: 9000, desc: '1.8초간 모든 피해 무효' },
  dash:     { name: '돌진', icon: '💨', cd: 5000, desc: '돌진하며 부딪힌 적에게 20 피해' },
  mine:     { name: '지뢰', icon: '💣', cd: 6000, desc: '지뢰 설치. 적이 밟으면 40 폭발' },
  heal:     { name: '치유', icon: '💚', cd: 10000, desc: '체력 30 회복' },
};
const SKILL_IDS = Object.keys(SKILLS);
const SKILL_META = SKILL_IDS.map(id => ({ id, ...SKILLS[id] }));

const WALLS = [
  { x: 440, y: 230, w: 120, h: 140 },
  { x: 180, y: 100, w: 30, h: 130 },
  { x: 790, y: 370, w: 30, h: 130 },
  { x: 180, y: 400, w: 130, h: 30 },
  { x: 690, y: 170, w: 130, h: 30 },
];
const SPAWNS = [[80, 80], [920, 520], [920, 80], [80, 520]];

// ---------- 수학 / 충돌 ----------
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const dist2 = (a, b) => (a.x - b.x) ** 2 + (a.y - b.y) ** 2;

function hitsWall(x, y, r) {
  for (const w of WALLS) {
    const cx = clamp(x, w.x, w.x + w.w), cy = clamp(y, w.y, w.y + w.h);
    if ((x - cx) ** 2 + (y - cy) ** 2 < r * r) return true;
  }
  return false;
}
function blocked(x, y, r) {
  return x < r || y < r || x > W - r || y > H - r || hitsWall(x, y, r);
}
function pushOutWalls(p) {
  for (const w of WALLS) {
    const cx = clamp(p.x, w.x, w.x + w.w), cy = clamp(p.y, w.y, w.y + w.h);
    let dx = p.x - cx, dy = p.y - cy;
    const d2 = dx * dx + dy * dy;
    if (d2 >= PR * PR) continue;
    if (d2 === 0) {
      // 중심이 벽 안: 가장 가까운 면으로 밀어냄
      const l = p.x - w.x, r = w.x + w.w - p.x, t = p.y - w.y, b = w.y + w.h - p.y;
      const m = Math.min(l, r, t, b);
      if (m === l) p.x = w.x - PR; else if (m === r) p.x = w.x + w.w + PR;
      else if (m === t) p.y = w.y - PR; else p.y = w.y + w.h + PR;
    } else {
      const d = Math.sqrt(d2);
      p.x = cx + (dx / d) * PR;
      p.y = cy + (dy / d) * PR;
    }
  }
}
function segDist2(px, py, x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const l2 = dx * dx + dy * dy || 1;
  const t = clamp(((px - x1) * dx + (py - y1) * dy) / l2, 0, 1);
  const qx = x1 + dx * t, qy = y1 + dy * t;
  return (px - qx) ** 2 + (py - qy) ** 2;
}

function rayBlocked(x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1, len = Math.hypot(dx, dy);
  for (let s = 8; s < len; s += 8) if (hitsWall(x1 + dx / len * s, y1 + dy / len * s, 2)) return true;
  return false;
}
function clearPath(x, y, a, len) {
  const cx = Math.cos(a), cy = Math.sin(a);
  for (let s = 10; s <= len; s += 10) if (blocked(x + cx * s, y + cy * s, PR + 2)) return false;
  return true;
}
function steer(x, y, ang, side) {
  for (const off of [0, 0.5, -0.5, 1.0, -1.0, 1.6, -1.6, 2.4, -2.4]) {
    const a = ang + off * side;
    if (clearPath(x, y, a, 60)) return a;
  }
  return ang;
}

// 봇 난이도: err=조준 오차(rad), think=조준 갱신 주기(ms), dodge=회피 확률, skill=틱당 능력 사용 확률,
// burst=[발사 ms, 휴식 ms], lead=이동 예측 사격, dist=선호 교전 거리
const DIFF = {
  easy:   { err: 0.32, think: 380, dodge: 0,    skill: 0.03, burst: [800, 1300], lead: false, dist: 300 },
  normal: { err: 0.14, think: 200, dodge: 0.45, skill: 0.10, burst: [1600, 500], lead: true,  dist: 260 },
  hard:   { err: 0.04, think: 90,  dodge: 1,    skill: 0.30, burst: null,        lead: true,  dist: 230 },
};

// ---------- WebSocket (RFC 6455 최소 구현) ----------
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
function wsFrame(op, payload) {
  const len = payload.length;
  let h;
  if (len < 126) h = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 126; h.writeUInt16BE(len, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(len), 2); }
  return Buffer.concat([h, payload]);
}
function parseFrame(buf) {
  if (buf.length < 2) return null;
  const fin = !!(buf[0] & 0x80), op = buf[0] & 0x0f, masked = !!(buf[1] & 0x80);
  let len = buf[1] & 0x7f, off = 2;
  if (len === 126) { if (buf.length < 4) return null; len = buf.readUInt16BE(2); off = 4; }
  else if (len === 127) {
    if (buf.length < 10) return null;
    const big = buf.readBigUInt64BE(2);
    if (big > 8192n) return { bad: true };
    len = Number(big); off = 10;
  }
  if (len > 8192) return { bad: true };
  let mask = null;
  if (masked) { if (buf.length < off + 4) return null; mask = buf.subarray(off, off + 4); off += 4; }
  if (buf.length < off + len) return null;
  const payload = Buffer.from(buf.subarray(off, off + len));
  if (mask) for (let i = 0; i < len; i++) payload[i] ^= mask[i & 3];
  return { fin, op, payload, used: off + len };
}

// ---------- 접속(= 플레이어) ----------
let nextId = 1;
const rooms = new Map();

class Client {
  constructor(socket) {
    this.id = nextId++;
    this.socket = socket;
    this.buf = Buffer.alloc(0);
    this.open = true;
    this.room = null;
    this.name = '플레이어' + this.id;
    this.skills = [];
    this.ready = false;
    this.wins = 0;
    this.slot = 0;
    this.lastMsg = 0;
    socket.on('data', d => this.onData(d));
    socket.on('close', () => this.onClose());
    socket.on('error', () => this.onClose());
    this.send({
      t: 'hello', id: this.id, W, H, walls: WALLS, skills: SKILL_META,
      maxPlayers: MAX_PLAYERS, winRounds: WIN_ROUNDS, maxHp: MAX_HP,
    });
  }
  onData(d) {
    this.buf = Buffer.concat([this.buf, d]);
    if (this.buf.length > 32768) return this.kill();
    for (;;) {
      const f = parseFrame(this.buf);
      if (!f) break;
      if (f.bad) return this.kill();
      this.buf = this.buf.subarray(f.used);
      if (f.op === 8) return this.kill();
      if (f.op === 9) { this.raw(wsFrame(10, f.payload)); continue; }
      if (f.op !== 1 || !f.fin) continue;
      let m;
      try { m = JSON.parse(f.payload.toString('utf8')); } catch (e) { continue; }
      if (m && typeof m === 'object') {
        try { this.handle(m); } catch (e) { console.error('handle error', e); }
      }
    }
  }
  raw(buf) { if (this.open) { try { this.socket.write(buf); } catch (e) { /* ignore */ } } }
  send(obj) { this.raw(wsFrame(1, Buffer.from(JSON.stringify(obj)))); }
  kill() { try { this.socket.destroy(); } catch (e) { /* ignore */ } this.onClose(); }
  onClose() {
    if (!this.open) return;
    this.open = false;
    leaveRoom(this);
  }
  handle(m) {
    switch (m.t) {
      case 'create': {
        if (this.room) return;
        this.setName(m.name);
        const r = new Room(makeCode());
        if (m.solo) r.solo = true;
        rooms.set(r.code, r);
        r.add(this);
        if (r.solo) r.setBots(1);
        break;
      }
      case 'join': {
        if (this.room) return;
        this.setName(m.name);
        const r = rooms.get(String(m.code || '').toUpperCase().trim());
        if (!r || r.solo) return this.send({ t: 'err', text: '방을 찾을 수 없어요' });
        r.add(this);
        break;
      }
      case 'bots': {
        const r = this.room;
        if (!r || !r.solo || r.phase !== 'lobby' || r.host !== this.id) return;
        if (['easy', 'normal', 'hard'].includes(m.diff)) r.diff = m.diff;
        r.setBots(clamp(Math.floor(Number(m.n) || 1), 1, MAX_PLAYERS - 1));
        break;
      }
      case 'leave': leaveRoom(this); break;
      case 'pick': {
        const r = this.room;
        if (!r || r.phase !== 'lobby') return;
        const s = m.skills;
        if (!Array.isArray(s) || s.length !== 2 || s[0] === s[1]) return;
        if (!SKILLS[s[0]] || !SKILLS[s[1]]) return;
        this.skills = [s[0], s[1]];
        this.ready = false;
        r.broadcastRoom();
        break;
      }
      case 'ready': {
        const r = this.room;
        if (!r || r.phase !== 'lobby' || r.host === this.id) return;
        this.ready = !this.ready;
        r.broadcastRoom();
        break;
      }
      case 'start': {
        const r = this.room;
        if (!r || r.phase !== 'lobby' || r.host !== this.id) return;
        if (r.players.length < 2) return this.send({ t: 'err', text: '2명 이상 필요해요' });
        if (r.players.some(p => p.id !== r.host && !p.ready)) return this.send({ t: 'err', text: '모두 준비해야 시작할 수 있어요' });
        r.startMatch();
        break;
      }
      case 'i': {
        const n = v => (Number.isFinite(v) ? v : 0);
        let mx = clamp(n(m.mx), -1, 1), my = clamp(n(m.my), -1, 1);
        const l = Math.hypot(mx, my);
        if (l > 1) { mx /= l; my /= l; }
        this.mx = mx; this.my = my;
        this.aim = n(m.a);
        this.fire = !!m.f; this.s1 = !!m.s1; this.s2 = !!m.s2;
        break;
      }
      default: break;
    }
  }
  setName(n) {
    n = String(n || '').replace(/[<>&"'`]/g, '').trim().slice(0, 10);
    this.name = n || ('플레이어' + this.id);
  }
}

function makeCode() {
  const A = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
  for (;;) {
    let c = '';
    for (let i = 0; i < 4; i++) c += A[Math.floor(Math.random() * A.length)];
    if (!rooms.has(c)) return c;
  }
}
function randomSkills() {
  const a = SKILL_IDS.slice().sort(() => Math.random() - 0.5);
  return [a[0], a[1]];
}
function newAi() {
  return { nextThink: 0, err: 0, side: 1, sideUntil: 0, strafe: 1, strafeUntil: 0, fireOn: true, fireUntil: 0, dodgeCool: 0, dodgeUntil: 0, dodgeAng: 0 };
}
// 솔로 연습용 봇 (네트워크 없이 플레이어와 같은 필드를 가짐)
class Bot {
  constructor() {
    this.id = nextId++;
    this.isBot = true;
    this.socket = { writableLength: 0 };
    this.open = true;
    this.room = null;
    this.name = '봇';
    this.skills = randomSkills();
    this.ready = true;
    this.wins = 0;
    this.slot = 0;
    this.mx = this.my = 0; this.aim = 0; this.fire = this.s1 = this.s2 = false;
    this.ai = newAi();
  }
  send() {}
  raw() {}
}
function leaveRoom(c) {
  const r = c.room;
  if (!r) return;
  c.room = null;
  r.players = r.players.filter(p => p !== c);
  if (r.players.length === 0 || r.players.every(p => p.isBot)) { rooms.delete(r.code); return; }
  if (r.host === c.id) r.host = r.players[0].id;
  if (r.phase !== 'lobby' && r.players.length < 2) {
    r.toLobby('상대가 나가서 대기실로 돌아갑니다');
  } else {
    r.broadcastRoom();
  }
}

// ---------- 방 ----------
class Room {
  constructor(code) {
    this.code = code;
    this.players = [];
    this.host = null;
    this.phase = 'lobby';
    this.phaseEnd = 0;
    this.round = 0;
    this.projs = [];
    this.mines = [];
    this.ev = [];
    this.last = Date.now();
    this.now = Date.now();
    this.solo = false;
    this.diff = 'normal';
  }
  add(c) {
    if (this.phase !== 'lobby') return c.send({ t: 'err', text: '이미 게임이 진행 중이에요' });
    if (this.players.length >= MAX_PLAYERS) return c.send({ t: 'err', text: '방이 가득 찼어요' });
    const used = new Set(this.players.map(p => p.slot));
    let slot = 0; while (used.has(slot)) slot++;
    c.slot = slot;
    c.room = this;
    c.skills = randomSkills();
    c.ready = false;
    c.wins = 0;
    c.mx = c.my = 0; c.aim = 0; c.fire = c.s1 = c.s2 = false;
    this.players.push(c);
    if (this.host === null) this.host = c.id;
    c.send({ t: 'joined', code: this.code, solo: this.solo });
    this.broadcastRoom();
  }
  setBots(n) {
    if (this.players.filter(p => p.isBot).length !== n) {
      this.players = this.players.filter(p => !p.isBot);
      for (let i = 0; i < n; i++) {
        const b = new Bot();
        const used = new Set(this.players.map(p => p.slot));
        let slot = 0; while (used.has(slot)) slot++;
        b.slot = slot; b.room = this; b.name = '봇' + (i + 1);
        this.players.push(b);
      }
    }
    this.broadcastRoom();
  }
  broadcastRoom() {
    const m = {
      t: 'room', code: this.code, host: this.host, phase: this.phase, round: this.round, solo: this.solo, diff: this.diff,
      players: this.players.map(p => ({ id: p.id, name: p.name, slot: p.slot, skills: p.skills, ready: p.ready, wins: p.wins, bot: !!p.isBot })),
    };
    for (const p of this.players) p.send(m);
  }
  broadcastMsg(text, kind) {
    for (const p of this.players) p.send({ t: 'msg', text, kind: kind || '' });
  }
  startMatch() {
    this.round = 1;
    for (const p of this.players) { p.wins = 0; }
    this.startRound();
  }
  startRound() {
    this.projs = []; this.mines = []; this.ev = [];
    this.players.forEach((p, i) => {
      const s = SPAWNS[p.slot % SPAWNS.length];
      p.x = s[0]; p.y = s[1];
      p.hp = MAX_HP; p.alive = true;
      p.cd = [0, 0, 0];
      p.shieldUntil = 0; p.slowUntil = 0; p.dash = null;
      p.mx = p.my = 0; p.fire = p.s1 = p.s2 = false;
      p.aim = (p.x < W / 2) ? 0 : Math.PI;
      if (p.isBot) p.ai = newAi();
    });
    this.phase = 'countdown';
    this.phaseEnd = Date.now() + 3000;
    this.last = Date.now();
    this.broadcastRoom();
  }
  toLobby(text) {
    this.phase = 'lobby';
    this.round = 0;
    this.projs = []; this.mines = []; this.ev = [];
    for (const p of this.players) {
      p.ready = !!p.isBot; p.wins = 0;
      if (p.isBot) p.skills = randomSkills();
    }
    this.broadcastRoom();
    if (text) this.broadcastMsg(text);
  }
  endRound(winner) {
    const now = Date.now();
    if (winner) winner.wins++;
    if (winner && winner.wins >= WIN_ROUNDS) {
      this.phase = 'matchEnd';
      this.phaseEnd = now + 6000;
      this.broadcastRoom();
      this.broadcastMsg(`🏆 ${winner.name} 최종 승리!`, 'match');
    } else {
      this.phase = 'roundEnd';
      this.phaseEnd = now + 3000;
      this.broadcastRoom();
      this.broadcastMsg(winner ? `${winner.name} 라운드 승리!` : '무승부!', 'round');
    }
  }

  tick(now) {
    const dt = Math.min(0.1, (now - this.last) / 1000);
    this.last = now;
    this.now = now;
    if (this.phase !== 'fight') {
      for (const p of this.players) if (p.isBot) { p.mx = p.my = 0; p.fire = p.s1 = p.s2 = false; }
    }
    if (this.phase === 'countdown') {
      if (now >= this.phaseEnd) { this.phase = 'fight'; this.broadcastRoom(); }
    } else if (this.phase === 'fight') {
      for (const p of this.players) if (p.isBot) this.botThink(p, now);
      this.simulate(now, dt, true);
      const alive = this.players.filter(p => p.alive);
      if (alive.length <= 1) this.endRound(alive[0] || null);
    } else if (this.phase === 'roundEnd') {
      this.simulate(now, dt, false);
      if (now >= this.phaseEnd) { this.round++; this.startRound(); }
    } else if (this.phase === 'matchEnd') {
      this.simulate(now, dt, false);
      if (now >= this.phaseEnd) this.toLobby();
    }
    if (this.phase !== 'lobby') this.snapshot(now);
  }

  botThink(b, now) {
    const D = DIFF[this.diff] || DIFF.normal, ai = b.ai;
    const foes = this.players.filter(q => q !== b && q.alive);
    if (!b.alive || !foes.length) { b.mx = b.my = 0; b.fire = b.s1 = b.s2 = false; return; }
    // 가장 가까운 적을 목표로
    let t = foes[0], bd = dist2(b, t);
    for (const q of foes) { const d2 = dist2(b, q); if (d2 < bd) { bd = d2; t = q; } }
    const d = Math.sqrt(bd) || 1;
    const los = !rayBlocked(b.x, b.y, t.x, t.y);
    if (now >= ai.nextThink) { ai.nextThink = now + D.think * (1 + Math.random() * 0.3); ai.err = (Math.random() * 2 - 1) * D.err; }
    if (now >= ai.sideUntil) { ai.side = Math.random() < 0.5 ? 1 : -1; ai.sideUntil = now + 1500 + Math.random() * 1500; }

    // 조준 (보통 이상은 상대 이동 방향을 예측)
    let tx = t.x, ty = t.y;
    if (D.lead) {
      const tt = d / 700, spd = BASE_SPEED * (t.slowUntil > now ? 0.5 : 1) * 0.8;
      tx += (t.mx || 0) * spd * tt; ty += (t.my || 0) * spd * tt;
    }
    const ang = Math.atan2(t.y - b.y, t.x - b.x);
    const aim = Math.atan2(ty - b.y, tx - b.x) + ai.err;

    // 날아오는 투사체 감지
    let threat = false, threatAng = 0;
    for (const pj of this.projs) {
      if (pj.owner === b.id) continue;
      const v2 = pj.vx * pj.vx + pj.vy * pj.vy || 1;
      const rx = b.x - pj.x, ry = b.y - pj.y;
      const tt = (rx * pj.vx + ry * pj.vy) / v2;
      if (tt < 0 || tt > 0.55) continue;
      const cx = pj.x + pj.vx * tt - b.x, cy = pj.y + pj.vy * tt - b.y;
      if (cx * cx + cy * cy < (PR + pj.r + 12) ** 2) {
        const side = (-pj.vy * rx + pj.vx * ry) >= 0 ? 1 : -1;
        threat = true; threatAng = Math.atan2(pj.vx * side, -pj.vy * side);
        break;
      }
    }
    if (threat && D.dodge > 0 && now >= ai.dodgeCool) {
      ai.dodgeCool = now + 600;
      if (Math.random() < D.dodge) { ai.dodgeUntil = now + 280; ai.dodgeAng = threatAng; }
    }

    // 이동: 접근 / 후퇴 / 좌우 이동
    let mv;
    if (ai.dodgeUntil > now) mv = ai.dodgeAng;
    else if (d > D.dist + 50 || !los) mv = ang;
    else if (d < D.dist - 70) mv = ang + Math.PI;
    else {
      if (now >= ai.strafeUntil) { ai.strafe = Math.random() < 0.5 ? 1 : -1; ai.strafeUntil = now + 800 + Math.random() * 1200; }
      mv = ang + ai.strafe * Math.PI / 2;
    }
    mv = steer(b.x, b.y, mv, ai.side);
    b.mx = Math.cos(mv); b.my = Math.sin(mv);

    // 기본 공격 (쉬움/보통은 끊어서 사격)
    let fire = los && d < 560;
    if (D.burst) {
      if (now >= ai.fireUntil) {
        ai.fireOn = !ai.fireOn;
        ai.fireUntil = now + D.burst[ai.fireOn ? 0 : 1] * (0.7 + Math.random() * 0.6);
      }
      fire = fire && ai.fireOn;
    }

    // 능력 사용 판단
    const hpr = b.hp / MAX_HP;
    const roll = () => Math.random() < D.skill;
    const want = sid => {
      switch (sid) {
        case 'fireball': return los && d < 480 && d > 90 && roll();
        case 'bolt': return los && d < 500 && roll();
        case 'nova': return d < 150 && roll();
        case 'dash': return los && d > 100 && d < 300 && roll();
        case 'blink': return (d < 110 || hpr < 0.35) && roll();
        case 'shield': return (threat || (los && d < 200 && hpr < 0.5)) && roll();
        case 'mine': return d < 320 && roll();
        case 'heal': return hpr <= 0.65 && roll();
        default: return false;
      }
    };
    let f = [want(b.skills[0]), want(b.skills[1])];
    let aimOut = aim;
    for (let i = 0; i < 2; i++) {
      if (b.skills[i] === 'blink' && f[i]) {
        // 순간이동은 적에게서 멀어지는 방향으로
        aimOut = steer(b.x, b.y, ang + Math.PI, ai.side);
        fire = false;
        f = [i === 0, i === 1];
      }
    }
    b.aim = aimOut; b.fire = fire; b.s1 = f[0]; b.s2 = f[1];
  }

  simulate(now, dt, canAct) {
    const ps = this.players;
    for (const p of ps) {
      if (!p.alive) continue;
      if (p.dash && now < p.dash.until) {
        p.x += p.dash.vx * dt; p.y += p.dash.vy * dt;
        for (const q of ps) {
          if (q === p || !q.alive || p.dash.hit.has(q.id)) continue;
          if (dist2(p, q) < (PR * 2 + 4) ** 2) { p.dash.hit.add(q.id); this.damage(q, 20, p.id); }
        }
      } else {
        p.dash = null;
        const spd = BASE_SPEED * (p.slowUntil > now ? 0.5 : 1);
        p.x += p.mx * spd * dt; p.y += p.my * spd * dt;
      }
      pushOutWalls(p);
      p.x = clamp(p.x, PR, W - PR); p.y = clamp(p.y, PR, H - PR);
    }
    // 플레이어끼리 겹침 방지
    for (let i = 0; i < ps.length; i++) for (let j = i + 1; j < ps.length; j++) {
      const a = ps[i], b = ps[j];
      if (!a.alive || !b.alive) continue;
      const dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy);
      if (d > 0 && d < PR * 2) {
        const push = (PR * 2 - d) / 2;
        a.x -= dx / d * push; a.y -= dy / d * push;
        b.x += dx / d * push; b.y += dy / d * push;
      }
    }
    if (canAct) for (const p of ps) if (p.alive) this.act(p, now);

    // 투사체
    for (let i = this.projs.length - 1; i >= 0; i--) {
      const b = this.projs[i];
      b.x += b.vx * dt; b.y += b.vy * dt; b.life -= dt;
      let remove = false;
      if (b.life <= 0 || b.x < 0 || b.x > W || b.y < 0 || b.y > H || hitsWall(b.x, b.y, b.r)) {
        remove = true;
        if (b.aoe) this.explode(b.x, b.y, b.aoe.r, b.aoe.dmg, b.owner, 0);
      } else {
        for (const q of ps) {
          if (!q.alive || q.id === b.owner) continue;
          if (dist2(b, q) < (b.r + PR) ** 2) {
            this.damage(q, b.dmg, b.owner);
            if (b.aoe) this.explode(b.x, b.y, b.aoe.r, b.aoe.dmg, b.owner, q.id);
            remove = true;
            break;
          }
        }
      }
      if (remove) this.projs.splice(i, 1);
    }
    // 지뢰
    for (let i = this.mines.length - 1; i >= 0; i--) {
      const m = this.mines[i];
      let remove = now >= m.expire;
      if (!remove && now >= m.armAt) {
        for (const q of ps) {
          if (!q.alive || q.id === m.owner) continue;
          if (dist2(m, q) < (PR + 24) ** 2) { this.explode(m.x, m.y, 75, 40, m.owner, 0); remove = true; break; }
        }
      }
      if (remove) this.mines.splice(i, 1);
    }
  }

  act(p, now) {
    if (p.fire && now >= p.cd[0]) {
      p.cd[0] = now + 320;
      const dx = Math.cos(p.aim), dy = Math.sin(p.aim);
      this.projs.push({ x: p.x + dx * 24, y: p.y + dy * 24, vx: dx * 700, vy: dy * 700, r: 6, dmg: 8, owner: p.id, life: 0.8, kind: 0, aoe: null });
    }
    for (let s = 1; s <= 2; s++) {
      const pressed = s === 1 ? p.s1 : p.s2;
      const sid = p.skills[s - 1];
      if (pressed && sid && now >= p.cd[s]) {
        if (this.cast(p, sid, now)) p.cd[s] = now + SKILLS[sid].cd;
      }
    }
  }

  cast(p, sid, now) {
    const dx = Math.cos(p.aim), dy = Math.sin(p.aim);
    const enemies = this.players.filter(q => q !== p && q.alive);
    switch (sid) {
      case 'fireball':
        this.projs.push({ x: p.x + dx * 26, y: p.y + dy * 26, vx: dx * 480, vy: dy * 480, r: 13, dmg: 28, owner: p.id, life: 1.6, kind: 1, aoe: { r: 70, dmg: 14 } });
        return true;
      case 'nova':
        this.ev.push({ k: 'nova', x: Math.round(p.x), y: Math.round(p.y), r: 150 });
        for (const q of enemies) {
          if (dist2(p, q) < (150 + PR) ** 2) { this.damage(q, 10, p.id); if (q.alive) q.slowUntil = now + 2500; }
        }
        return true;
      case 'bolt': {
        let len = 0;
        while (len < 520 && !hitsWall(p.x + dx * len, p.y + dy * len, 2)) len += 6;
        const x2 = p.x + dx * len, y2 = p.y + dy * len;
        this.ev.push({ k: 'beam', x1: Math.round(p.x), y1: Math.round(p.y), x2: Math.round(x2), y2: Math.round(y2) });
        for (const q of enemies) {
          if (segDist2(q.x, q.y, p.x, p.y, x2, y2) < (PR + 10) ** 2) this.damage(q, 26, p.id);
        }
        return true;
      }
      case 'blink': {
        let nx = p.x, ny = p.y;
        for (let d = 6; d <= 220; d += 6) {
          const tx = p.x + dx * d, ty = p.y + dy * d;
          if (blocked(tx, ty, PR)) break;
          nx = tx; ny = ty;
        }
        if (nx === p.x && ny === p.y) return false;
        this.ev.push({ k: 'blink', x1: Math.round(p.x), y1: Math.round(p.y), x2: Math.round(nx), y2: Math.round(ny) });
        p.x = nx; p.y = ny;
        return true;
      }
      case 'shield':
        p.shieldUntil = now + 1800;
        return true;
      case 'dash':
        p.dash = { vx: dx * 1500, vy: dy * 1500, until: now + 200, hit: new Set() };
        return true;
      case 'mine': {
        const mine = this.mines.filter(m => m.owner === p.id);
        if (mine.length >= 3) this.mines.splice(this.mines.indexOf(mine[0]), 1);
        this.mines.push({ x: p.x, y: p.y, owner: p.id, armAt: now + 800, expire: now + 12000 });
        return true;
      }
      case 'heal':
        p.hp = Math.min(MAX_HP, p.hp + 30);
        this.ev.push({ k: 'heal', x: Math.round(p.x), y: Math.round(p.y) });
        return true;
      default:
        return false;
    }
  }

  damage(q, dmg, ownerId) {
    if (!q.alive) return;
    const x = Math.round(q.x), y = Math.round(q.y);
    if (q.shieldUntil > this.now) { this.ev.push({ k: 'block', x, y }); return; }
    q.hp -= dmg;
    this.ev.push({ k: 'hit', x, y });
    if (q.hp <= 0) {
      q.hp = 0; q.alive = false;
      this.ev.push({ k: 'die', x, y });
    }
  }

  explode(x, y, r, dmg, owner, excludeId) {
    this.ev.push({ k: 'boom', x: Math.round(x), y: Math.round(y), r });
    for (const q of this.players) {
      if (!q.alive || q.id === owner || q.id === excludeId) continue;
      if (dist2({ x, y }, q) < (r + PR) ** 2) this.damage(q, dmg, owner);
    }
  }

  snapshot(now) {
    const s = {
      t: 's', ph: this.phase, tm: Math.max(0, this.phaseEnd - now),
      p: this.players.map(p => [
        p.id, Math.round(p.x), Math.round(p.y), +p.aim.toFixed(2), Math.max(0, Math.ceil(p.hp)),
        (p.alive ? 1 : 0) | (p.shieldUntil > now ? 2 : 0) | (p.slowUntil > now ? 4 : 0) | (p.dash && now < p.dash.until ? 8 : 0),
        Math.max(0, Math.ceil(p.cd[1] - now)), Math.max(0, Math.ceil(p.cd[2] - now)),
      ]),
      b: this.projs.map(b => [Math.round(b.x), Math.round(b.y), b.r, b.kind, b.owner, Math.round(b.vx), Math.round(b.vy)]),
      m: this.mines.map(m => [Math.round(m.x), Math.round(m.y), m.owner, now >= m.armAt ? 1 : 0]),
      e: this.ev,
    };
    this.ev = [];
    const buf = wsFrame(1, Buffer.from(JSON.stringify(s)));
    for (const p of this.players) {
      if (p.socket.writableLength > 262144) continue; // 느린 연결은 건너뜀
      p.raw(buf);
    }
  }
}

setInterval(() => {
  const now = Date.now();
  for (const r of rooms.values()) if (r.phase !== 'lobby') r.tick(now);
}, 33);

// ---------- HTTP ----------
const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/' || url === '/index.html') {
    fs.readFile(path.join(__dirname, 'index.html'), (err, data) => {
      if (err) { res.writeHead(500); return res.end('index.html not found'); }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(data);
    });
  } else if (url === '/health') {
    res.writeHead(200); res.end('ok');
  } else {
    res.writeHead(404); res.end('not found');
  }
});
server.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  if (!key || String(req.headers.upgrade || '').toLowerCase() !== 'websocket') { socket.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  socket.setNoDelay(true);
  new Client(socket);
});
// 유휴 연결 유지(Render 등 프록시 대응)
setInterval(() => {
  const ping = wsFrame(9, Buffer.alloc(0));
  for (const r of rooms.values()) for (const p of r.players) p.raw(ping);
}, 25000);

server.listen(PORT, () => console.log('Ability Arena server on :' + PORT));
