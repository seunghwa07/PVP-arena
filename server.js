'use strict';
// 능력 대전 아레나 - 서버 (외부 패키지 없이 동작: 내장 WebSocket 구현)
// 근접 전투판: 큰 맵 + 콤보 베기 + 넉백/기절 + 줄어드는 자기장
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
// 현재 처리 중인 방의 맵 (Room.tick / startRound 시작 때 useMap()으로 바꿔 끼워요. 노드는 한 번에 하나씩만 처리하므로 안전해요)
let W = 3200, H = 2000, WALLS = [], SPAWNS = [];   // 클라이언트는 1400x800 초과 시 캐릭터 추적 카메라 사용
const PR = 18;                    // 플레이어 반지름
const BASE_SPEED = 312;   // 기존 260의 1.2배
const MAX_HP = 100;
const MAX_PLAYERS = 4;
const WIN_ROUNDS = 3;             // 3라운드 선승

// 기본 공격: 3연타 콤보 (3타째는 강타)
const ATK = {
  cd: 380, range: 64, arc: 2.0, dmg: 12, kb: 170,
  hCd: 620, hRange: 78, hArc: 2.6, hDmg: 22, hKb: 380,
  comboWindow: 800,
};
// 자기장: 전투 시작 15초 뒤부터 80초에 걸쳐 중앙으로 줄어듦. 밖에 있으면 초당 8 피해
let ZONE = { delay: 15, shrink: 80, fw: 560, fh: 380, dps: 8 };   // 맵마다 다름 (MAPS[].zone)

// ---------- 능력 정의 (클라이언트에도 전달) ----------
const SKILLS = {
  dash:   { name: '돌진 베기', icon: '💨', cd: 5000, desc: '가까운 적에게 돌진하며 22 피해 + 밀쳐냄' },
  whirl:  { name: '회전 베기', icon: '🌪️', cd: 4500, desc: '주변 360° 16 피해 + 밀쳐냄' },
  slam:   { name: '대지 강타', icon: '🔨', cd: 7000, desc: '내려쳐 20 피해, 크게 밀쳐내고 0.6초 기절' },
  parry:  { name: '받아치기', icon: '⚔️', cd: 5000, desc: '0.45초 안에 맞으면 무효, 공격자 1초 기절' },
  shield: { name: '방어막', icon: '🛡️', cd: 9000, desc: '1.8초간 모든 피해 무효' },
  blink:  { name: '순간이동', icon: '🌀', cd: 4000, desc: '이동하는 방향으로 순간 이동 (가만히 있으면 적의 반대로)' },
  heal:   { name: '치유', icon: '💚', cd: 10000, desc: '체력 30 회복' },
  throw:  { name: '단검 투척', icon: '🗡️', cd: 2500, desc: '가까운 적에게 단검을 던져 14 피해' },
  nova:   { name: '서리 폭발', icon: '❄️', cd: 6000, desc: '주변 적에게 10 피해 + 2.5초 둔화' },
};
const AVATARS = ['🐱', '🐶', '🦊', '🐼', '🐯', '🐸', '🐙', '🦄', '🐲', '🦉', '🐧', '🦈']; // 프로필 아바타 (클라이언트에는 번호만 오감)
// 맵에 랜덤하게 나타나는 버프. dur=0이면 즉시 효과
const BUFFS = [
  { id: 'heal',  icon: '💚', name: '회복',         color: '#6be585', dur: 0 },
  { id: 'speed', icon: '⚡', name: '속도 증가',     color: '#ffe066', dur: 6000 },
  { id: 'power', icon: '🔥', name: '공격력 증가',   color: '#ff7a5c', dur: 8000 },
  { id: 'cdr',   icon: '⏱️', name: '쿨타임 초기화', color: '#9be7ff', dur: 0 },
];
const BUFF_WEIGHT = [35, 30, 20, 15];   // 등장 확률 비중
const PICK = { first: [5000, 9000], every: [7000, 14000], max: 4, life: 28000, r: 26, healAmt: 35, speedMul: 1.45, powerMul: 1.4 };
const LOOK_N = [8, 8, 7];   // 캐릭터 외형 개수: [얼굴, 모자, 칼 스킨] (클라이언트 목록과 같아야 해요)
const THEME_N = 7;          // 프로필 카드 배경 개수
const SKILL_IDS = Object.keys(SKILLS);
const SKILL_META = SKILL_IDS.map(id => ({ id, ...SKILLS[id] }));

// ---------- 맵 정의 ----------
// 맵 = { id, name, icon, desc, style, W, H, walls, spawns, zone, pickMax, rooms?, doors?, nav? }
// 새 맵을 추가하려면 build 함수를 만들어 아래 MAPS에 넣으면 돼요 (클라이언트 선택 목록에 자동으로 나타나요)

// (1) 기존 맵: 풀밭 아레나. 왼쪽 위 1/4만 정의하고 좌우/상하로 대칭 복제 (+ 중앙 요새)
function buildArena() {
  const w = 3200, h = 2000;
  const QUAD = [
    { x: 360, y: 300, w: 220, h: 34 }, { x: 360, y: 300, w: 34, h: 220 },   // ㄱ자 엄폐물
    { x: 800, y: 200, w: 34, h: 260 },
    { x: 1100, y: 120, w: 400, h: 34 },                                       // 위쪽 긴 벽
    { x: 1000, y: 420, w: 240, h: 34 },
    { x: 600, y: 700, w: 34, h: 240 },
    { x: 880, y: 620, w: 70, h: 70 }, { x: 1250, y: 720, w: 70, h: 70 }, { x: 1380, y: 280, w: 70, h: 70 }, // 기둥
    { x: 1160, y: 860, w: 200, h: 34 },
  ];
  const walls = [{ x: 1450, y: 880, w: 300, h: 240 }];                        // 중앙 요새
  for (const q of QUAD) {
    walls.push(q);
    walls.push({ x: w - q.x - q.w, y: q.y, w: q.w, h: q.h });
    walls.push({ x: q.x, y: h - q.y - q.h, w: q.w, h: q.h });
    walls.push({ x: w - q.x - q.w, y: h - q.y - q.h, w: q.w, h: q.h });
  }
  return {
    id: 'arena', name: '풀밭 아레나', icon: '🌳', desc: '탁 트인 풀밭에 돌 엄폐물이 흩어진 기본 맵', style: 'field',
    W: w, H: h, walls,
    spawns: [[140, 140], [w - 140, h - 140], [w - 140, 140], [140, h - 140]],
    zone: { delay: 15, shrink: 80, fw: 560, fh: 380, dps: 8 }, pickMax: 4,
  };
}

// (2) 신규 맵: 대형 빌딩 (4800x3000). 방 + 문 + 복도 + 중앙 아트리움.
//     왼쪽 위 1/4(과 축 위의 방)만 정의하고 대칭 복제해요. 복도 폭 200 이상, 문 폭 120~200이라 캐릭터(지름 36)가 편하게 지나가요.
function buildTower() {
  const w = 4800, h = 3000, T = 40;                 // T = 벽 두께
  const walls = [], rooms = [], doors = [];
  // [a, b] 구간에서 틈(gaps)을 뺀 조각들
  const cut = (a, b, gaps) => {
    let segs = [[a, b]];
    for (const [g0, g1] of gaps) {
      const next = [];
      for (const [s0, s1] of segs) {
        if (g1 <= s0 || g0 >= s1) { next.push([s0, s1]); continue; }
        if (g0 > s0) next.push([s0, g0]);
        if (g1 < s1) next.push([g1, s1]);
      }
      segs = next;
    }
    return segs;
  };
  // 방 하나: 사방 벽 + 문(틈). 문 좌표는 절대 좌표 (N/S 변은 x 구간, W/E 변은 y 구간)
  const room = (x, y, rw, rh, d, floor) => {
    const o = { walls: [], doors: [], rooms: [{ x, y, w: rw, h: rh, k: floor }] };
    for (const [a, b] of cut(x, x + rw, d.N || [])) o.walls.push({ x: a, y, w: b - a, h: T });
    for (const [a, b] of cut(x, x + rw, d.S || [])) o.walls.push({ x: a, y: y + rh - T, w: b - a, h: T });
    for (const [a, b] of cut(y + T, y + rh - T, d.W || [])) o.walls.push({ x, y: a, w: T, h: b - a });
    for (const [a, b] of cut(y + T, y + rh - T, d.E || [])) o.walls.push({ x: x + rw - T, y: a, w: T, h: b - a });
    for (const [a, b] of d.N || []) o.doors.push({ x: a, y, w: b - a, h: T });
    for (const [a, b] of d.S || []) o.doors.push({ x: a, y: y + rh - T, w: b - a, h: T });
    for (const [a, b] of d.W || []) o.doors.push({ x, y: a, w: T, h: b - a });
    for (const [a, b] of d.E || []) o.doors.push({ x: x + rw - T, y: a, w: T, h: b - a });
    return o;
  };
  const prop = (x, y, pw, ph, kind) => ({ walls: [{ x, y, w: pw, h: ph, p: kind }], doors: [], rooms: [] });  // 기둥(1) / 가구(2)
  const mX = r => ({ ...r, x: w - r.x - r.w });
  const mY = r => ({ ...r, y: h - r.y - r.h });
  const seen = new Set();
  const addTo = (list, tag, r) => { const k = tag + [r.x, r.y, r.w, r.h, r.p || 0, r.k || 0].join(','); if (!seen.has(k)) { seen.add(k); list.push(r); } };
  // mode: 'q' 4방향 복제 / 'x' 좌우 / 'y' 상하 / '' 그대로 (축 위에 걸친 방은 문 위치가 대칭이라 한쪽만 복제)
  const place = (g, mode) => {
    const fx = mode === 'q' || mode === 'x', fy = mode === 'q' || mode === 'y';
    const vs = [r => r];
    if (fx) vs.push(mX);
    if (fy) vs.push(mY);
    if (fx && fy) vs.push(r => mY(mX(r)));
    for (const f of vs) {
      for (const r of g.walls) addTo(walls, 'w', f(r));
      for (const r of g.doors) addTo(doors, 'd', f(r));
      for (const r of g.rooms) addTo(rooms, 'r', f(r));
    }
  };

  // 방 바닥 종류 k: 1 파란 카펫 / 2 원목 / 3 연구실 타일 / 4 아트리움 대리석
  // --- 4방향 복제되는 방 (왼쪽 위 1/4 안쪽) ---
  place(room(0, 0, 800, 600, { E: [[190, 350]], S: [[300, 460]] }, 3), 'q');                                    // 출발 방
  place(room(1040, 0, 860, 500, { W: [[190, 350]], E: [[190, 350]], S: [[1250, 1430]] }, 2), 'q');             // 북쪽 사무실
  place(room(0, 800, 620, 300, { N: [[250, 400]], E: [[880, 1020]] }, 1), 'q');                                 // 서쪽 회의실
  place(room(1100, 760, 600, 420, { N: [[1250, 1420]], S: [[1250, 1420]], W: [[880, 1040]], E: [[880, 1040]] }, 2), 'q'); // 중앙 사무실
  // --- 축 위의 방 ---
  place(room(2100, 0, 600, 420, { W: [[160, 300]], E: [[160, 300]], S: [[2290, 2510]] }, 1), 'y');              // 위·아래 중앙 로비
  place(room(2200, 620, 400, 300, { W: [[710, 850]], E: [[710, 850]], N: [[2330, 2470]], S: [[2330, 2470]] }, 3), 'y'); // 보안실
  place(room(0, 1300, 420, 400, { N: [[140, 280]], S: [[140, 280]], E: [[1400, 1600]] }, 3), 'x');             // 좌우 끝 방
  // --- 중앙 아트리움 ---
  place(room(1900, 1100, 1000, 800, { N: [[2300, 2500]], S: [[2300, 2500]], W: [[1400, 1600]], E: [[1400, 1600]] }, 4), '');
  place(prop(2090, 1240, 90, 90, 1), 'q');         // 아트리움 기둥 4개
  place(prop(2330, 1430, 140, 140, 2), '');        // 중앙 안내 데스크
  // --- 복도 / 로비 가구 (엄폐물) ---
  for (const [x, y, pw, ph, k] of [
    [880, 960, 70, 70, 1], [700, 1260, 70, 70, 1], [1000, 1260, 70, 70, 1], [1480, 600, 60, 60, 1], [1990, 800, 70, 70, 1],
    [780, 1400, 240, 36, 2], [1250, 1330, 260, 36, 2], [1650, 1260, 36, 200, 2],
  ]) place(prop(x, y, pw, ph, k), 'q');

  return {
    id: 'tower', name: '대형 빌딩', icon: '🏢', desc: '방·문·복도로 이어진 거대한 건물. 중앙 아트리움에서 마지막 결전', style: 'building',
    W: w, H: h, walls, rooms, doors,
    spawns: [[140, 140], [w - 140, h - 140], [w - 140, 140], [140, h - 140]],
    zone: { delay: 20, shrink: 120, fw: 900, fh: 560, dps: 8 }, pickMax: 6,
    nav: true,   // 봇이 벽 너머 적을 찾아갈 때 길찾기 사용
  };
}

// ---------- 수학 / 충돌 ----------
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const dist2 = (a, b) => (a.x - b.x) ** 2 + (a.y - b.y) ** 2;
const angDiff = (a, b) => Math.atan2(Math.sin(a - b), Math.cos(a - b));

function hitsWall(x, y, r) {
  for (const w of WALLS) {
    if (x + r < w.x || x - r > w.x + w.w || y + r < w.y || y - r > w.y + w.h) continue;
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

// 봇 난이도: err=조준 오차(rad), think=조준 갱신 주기(ms), dodge=투척 회피 확률, skill=틱당 능력 사용 확률,
// burst=[공격 ms, 휴식 ms], lead=이동 예측, dist=선호 교전 거리, retreat=간격 조절(치고 빠지기)
const DIFF = {
  easy:   { err: 0.32, think: 380, dodge: 0,    skill: 0.03, burst: [800, 1300], lead: false, dist: 40, retreat: false },
  normal: { err: 0.14, think: 200, dodge: 0.45, skill: 0.10, burst: [1600, 500], lead: true,  dist: 55, retreat: false },
  hard:   { err: 0.04, think: 90,  dodge: 1,    skill: 0.30, burst: null,        lead: true,  dist: 72, retreat: true },
};

// ---------- 맵 등록 / 전환 ----------
const MAPS = { arena: buildArena(), tower: buildTower() };
const MAP_ORDER = ['arena', 'tower'];
const MAP_LIST = MAP_ORDER.map(id => { const m = MAPS[id]; return { id, name: m.name, icon: m.icon, desc: m.desc, W: m.W, H: m.H }; });
for (const id of MAP_ORDER) {   // 클라이언트에 보낼 맵 데이터 (한 번만 만들어 둠)
  const m = MAPS[id];
  m.payload = JSON.stringify({ t: 'mapdata', id, style: m.style, W: m.W, H: m.H, walls: m.walls, rooms: m.rooms || [], doors: m.doors || [] });
}
function useMap(m) { W = m.W; H = m.H; WALLS = m.walls; SPAWNS = m.spawns; ZONE = m.zone; }
useMap(MAPS.arena);

// ---------- 봇 길찾기 (nav: true 인 맵에서만) ----------
// 맵을 NAV px 칸으로 나누고, 목표에서 BFS로 거리장을 만든 뒤 내려가는 방향으로 따라가요.
const NAV = 40;
function navGrid(m) {
  if (m.navg) return m.navg;
  useMap(m);
  const cols = Math.ceil(m.W / NAV), rows = Math.ceil(m.H / NAV), ok = new Uint8Array(cols * rows);
  for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) ok[r * cols + c] = blocked((c + 0.5) * NAV, (r + 0.5) * NAV, PR + 4) ? 0 : 1;
  return (m.navg = { cols, rows, ok });
}
function nearestOk(g, cx, cy) {
  cx = clamp(cx, 0, g.cols - 1); cy = clamp(cy, 0, g.rows - 1);
  if (g.ok[cy * g.cols + cx]) return [cx, cy];
  for (let rad = 1; rad <= 6; rad++) {
    for (let dy = -rad; dy <= rad; dy++) for (let dx = -rad; dx <= rad; dx++) {
      if (Math.max(Math.abs(dx), Math.abs(dy)) !== rad) continue;
      const x = cx + dx, y = cy + dy;
      if (x >= 0 && y >= 0 && x < g.cols && y < g.rows && g.ok[y * g.cols + x]) return [x, y];
    }
  }
  return null;
}
const NAV_DIRS = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
function segClear(x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1, len = Math.hypot(dx, dy);
  for (let s = 12; s < len; s += 12) if (blocked(x1 + dx / len * s, y1 + dy / len * s, PR + 2)) return false;
  return true;
}
// (x,y)에서 (gx,gy)로 가는 길의 다음 진행 각도. 길이 없으면 null
function navAngle(m, x, y, gx, gy) {
  const g = navGrid(m);
  const goal = nearestOk(g, Math.floor(gx / NAV), Math.floor(gy / NAV));
  const start = nearestOk(g, Math.floor(x / NAV), Math.floor(y / NAV));
  if (!goal || !start) return null;
  const { cols, rows, ok } = g, dist = new Int32Array(cols * rows).fill(-1), q = new Int32Array(cols * rows);
  let head = 0, tail = 0;
  const gi = goal[1] * cols + goal[0], si = start[1] * cols + start[0];
  dist[gi] = 0; q[tail++] = gi;
  while (head < tail && dist[si] < 0) {
    const cur = q[head++], cx = cur % cols, cy = (cur / cols) | 0;
    for (const [dx, dy] of NAV_DIRS) {
      const nx = cx + dx, ny = cy + dy;
      if (nx < 0 || ny < 0 || nx >= cols || ny >= rows) continue;
      const ni = ny * cols + nx;
      if (!ok[ni] || dist[ni] >= 0) continue;
      if (dx && dy && !(ok[cy * cols + nx] && ok[ny * cols + cx])) continue;   // 모서리 끼임 방지
      dist[ni] = dist[cur] + 1; q[tail++] = ni;
    }
  }
  if (dist[si] < 0) return null;
  let cur = si, first = null, best = null;
  for (let step = 0; step < 14 && dist[cur] > 0; step++) {
    const cx = cur % cols, cy = (cur / cols) | 0;
    let nb = -1, nd = dist[cur];
    for (const [dx, dy] of NAV_DIRS) {
      const nx = cx + dx, ny = cy + dy;
      if (nx < 0 || ny < 0 || nx >= cols || ny >= rows) continue;
      const ni = ny * cols + nx;
      if (dist[ni] >= 0 && dist[ni] < nd && (!(dx && dy) || (ok[cy * cols + nx] && ok[ny * cols + cx]))) { nd = dist[ni]; nb = ni; }
    }
    if (nb < 0) break;
    cur = nb;
    const px = ((cur % cols) + 0.5) * NAV, py = (((cur / cols) | 0) + 0.5) * NAV;
    if (!first) first = [px, py];
    if (segClear(x, y, px, py)) best = [px, py];
  }
  const t = best || first;
  return t ? Math.atan2(t[1] - y, t[0] - x) : null;
}

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
    this.av = this.id % AVATARS.length;
    this.look = [0, 0, 0];
    this.bio = '';
    this.th = 0;
    this.skills = [];
    this.ready = false;
    this.wins = 0;
    this.slot = 0;
    this.lastMsg = 0;
    socket.on('data', d => this.onData(d));
    socket.on('close', () => this.onClose());
    socket.on('error', () => this.onClose());
    this.send({
      t: 'hello', id: this.id, W: MAPS.arena.W, H: MAPS.arena.H, walls: MAPS.arena.walls, maps: MAP_LIST, skills: SKILL_META,
      maxPlayers: MAX_PLAYERS, winRounds: WIN_ROUNDS, maxHp: MAX_HP,
      avatars: AVATARS, buffs: BUFFS, speed: BASE_SPEED, atk: { range: ATK.range, arc: ATK.arc, hRange: ATK.hRange, hArc: ATK.hArc },
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
        this.setProfile(m);
        const r = new Room(makeCode());
        if (m.solo) r.solo = true;
        rooms.set(r.code, r);
        r.add(this);
        if (r.solo) r.setBots(1);
        break;
      }
      case 'join': {
        if (this.room) return;
        this.setProfile(m);
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
      case 'map': {
        const r = this.room;
        if (!r || r.phase !== 'lobby' || r.host !== this.id) return;
        if (!MAPS[m.id]) return;
        r.mapId = m.id; r.map = MAPS[m.id];
        r.sendMap();
        r.broadcastRoom();
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
      case 'ping': this.send({ t: 'pong', c: Number(m.c) || 0 }); break;
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
  setProfile(m) {
    this.setName(m.name);
    const a = Number(m.av);
    this.av = Number.isInteger(a) && a >= 0 && a < AVATARS.length ? a : this.id % AVATARS.length;
    const L = Array.isArray(m.look) ? m.look : [];
    this.look = LOOK_N.map((n, i) => { const v = Number(L[i]); return Number.isInteger(v) && v >= 0 && v < n ? v : 0; });
    this.bio = String(m.bio || '').replace(/[<>&"'`]/g, '').trim().slice(0, 14);
    const t = Number(m.th);
    this.th = Number.isInteger(t) && t >= 0 && t < THEME_N ? t : 0;
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
  return { nextThink: 0, err: 0, side: 1, sideUntil: 0, strafe: 1, strafeUntil: 0, fireOn: true, fireUntil: 0, dodgeCool: 0, dodgeUntil: 0, dodgeAng: 0, navUntil: 0, navAng: 0 };
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
    this.av = -1;
    this.look = LOOK_N.map(n => Math.floor(Math.random() * n));
    this.bio = '';
    this.th = 0;
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
    this.ev = [];
    this.last = Date.now();
    this.now = Date.now();
    this.fightAt = 0;
    this.pickups = []; this.nextPickup = 0; this.pid = 1; this.src = 'sword';
    this.solo = false;
    this.diff = 'normal';
    this.mapId = 'arena'; this.map = MAPS.arena;
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
    this.sendMap(c);
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
  sendMap(only) {
    const buf = wsFrame(1, Buffer.from(this.map.payload));
    for (const p of only ? [only] : this.players) p.raw(buf);
  }
  broadcastRoom() {
    // 다른 사람이 고른 스킬은 보내지 않음(본인 것만 전송)
    for (const q of this.players) {
      q.send({
        t: 'room', code: this.code, host: this.host, phase: this.phase, round: this.round, solo: this.solo, diff: this.diff, map: this.mapId,
        players: this.players.map(p => ({ id: p.id, name: p.name, av: p.av, look: p.look, bio: p.bio, th: p.th, slot: p.slot, skills: p === q ? p.skills : [], ready: p.ready, wins: p.wins, bot: !!p.isBot })),
      });
    }
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
    useMap(this.map);
    this.sendMap();   // 클라이언트가 이 방의 맵을 그리도록
    this.projs = []; this.ev = [];
    this.pickups = []; this.nextPickup = 0;
    this.fightAt = 0;
    this.players.forEach(p => {
      const s = SPAWNS[p.slot % SPAWNS.length];
      p.x = s[0]; p.y = s[1];
      p.hp = MAX_HP; p.alive = true;
      p.cd = [0, 0, 0];
      p.shieldUntil = 0; p.slowUntil = 0; p.dash = null;
      p.stunUntil = 0; p.parryUntil = 0; p.kv = null; p.atkSlowUntil = 0; p.speedUntil = 0; p.powerUntil = 0;
      p.combo = 0; p.comboUntil = 0; p.svx = p.svy = 0;
      p.mx = p.my = 0; p.fire = p.s1 = p.s2 = false;
      p.aim = Math.atan2(H / 2 - p.y, W / 2 - p.x);
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
    this.projs = []; this.ev = []; this.pickups = [];
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

  // 현재 안전지대 [x1, y1, x2, y2]
  zone(now) {
    if (!this.fightAt) return [0, 0, W, H];
    const k = clamp(((now - this.fightAt) / 1000 - ZONE.delay) / ZONE.shrink, 0, 1);
    const x0 = W / 2 - ZONE.fw / 2, y0 = H / 2 - ZONE.fh / 2, x1 = W / 2 + ZONE.fw / 2, y1 = H / 2 + ZONE.fh / 2;
    return [x0 * k, y0 * k, W + (x1 - W) * k, H + (y1 - H) * k];
  }

  tick(now) {
    useMap(this.map);
    const dt = Math.min(0.1, (now - this.last) / 1000);
    this.last = now;
    this.now = now;
    if (this.phase !== 'fight') {
      for (const p of this.players) if (p.isBot) { p.mx = p.my = 0; p.fire = p.s1 = p.s2 = false; }
    }
    if (this.phase === 'countdown') {
      if (now >= this.phaseEnd) {
        this.phase = 'fight'; this.fightAt = now; this.broadcastRoom();
        this.nextPickup = now + PICK.first[0] + Math.random() * (PICK.first[1] - PICK.first[0]);
      }
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

    // 조준 (보통 이상은 상대 이동 방향을 조금 앞서 노림)
    let tx = t.x, ty = t.y;
    if (D.lead) {
      const spd = BASE_SPEED * (t.slowUntil > now ? 0.5 : 1);
      tx += (t.mx || 0) * spd * 0.12; ty += (t.my || 0) * spd * 0.12;
    }
    const ang = Math.atan2(t.y - b.y, t.x - b.x);
    const aim = Math.atan2(ty - b.y, tx - b.x) + ai.err;

    // 날아오는 단검 감지
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

    // 자기장이 줄어들었다면 가장자리에서 중앙으로 복귀
    const z = this.zone(now);
    const shrunk = z[0] > 1;
    const zoneRush = shrunk && (b.x < z[0] + 70 || b.x > z[2] - 70 || b.y < z[1] + 70 || b.y > z[3] - 70);

    // 이동: 접근 / 간격 조절 / 좌우 이동
    let mv;
    if (ai.dodgeUntil > now) mv = ai.dodgeAng;
    else if (zoneRush) mv = this.map.nav ? this.navTo(b, now, W / 2, H / 2, Math.atan2(H / 2 - b.y, W / 2 - b.x)) : Math.atan2(H / 2 - b.y, W / 2 - b.x);
    else if (d > D.dist + 25 || !los) mv = (!los && this.map.nav) ? this.navTo(b, now, t.x, t.y, ang) : ang;
    else if (D.retreat && d < D.dist - 30) mv = ang + Math.PI;
    else {
      if (now >= ai.strafeUntil) { ai.strafe = Math.random() < 0.5 ? 1 : -1; ai.strafeUntil = now + 800 + Math.random() * 1200; }
      mv = ang + ai.strafe * Math.PI / 2;
    }
    if (this.diff !== 'easy' && ai.dodgeUntil <= now && !zoneRush && d > 140) {
      let tu = null, tb = 600 * 600;
      for (const u of this.pickups) {
        if (u.type === 0 && b.hp > MAX_HP * 0.85) continue;
        const d2 = dist2(b, u);
        if (d2 < tb && !rayBlocked(b.x, b.y, u.x, u.y)) { tb = d2; tu = u; }
      }
      if (tu) mv = Math.atan2(tu.y - b.y, tu.x - b.x);
    }
    mv = steer(b.x, b.y, mv, ai.side);
    b.mx = Math.cos(mv); b.my = Math.sin(mv);

    // 기본 공격 (쉬움/보통은 끊어서 휘두름)
    let fire = los && d < ATK.range + PR + 8;
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
        case 'dash': return los && d > 120 && d < 320 && roll();
        case 'whirl': return d < 90 && roll();
        case 'slam': return d < 105 && roll();
        case 'parry': return (threat || d < 100) && Math.random() < D.skill * 0.6;
        case 'shield': return (threat || (los && d < 120 && hpr < 0.5)) && roll();
        case 'blink': return ((d < 90 && hpr < 0.35) || zoneRush) && roll();
        case 'heal': return hpr <= 0.6 && roll();
        case 'throw': return los && d > 130 && d < 520 && roll();
        case 'nova': return d < 140 && roll();
        default: return false;
      }
    };
    let f = [want(b.skills[0]), want(b.skills[1])];
    let aimOut = aim;
    for (let i = 0; i < 2; i++) {
      if (b.skills[i] === 'blink' && f[i]) {
        // 순간이동: 자기장 밖이면 중앙으로, 아니면 적에게서 멀어지는 방향으로
        aimOut = zoneRush ? Math.atan2(H / 2 - b.y, W / 2 - b.x) : steer(b.x, b.y, ang + Math.PI, ai.side);
        fire = false;
        f = [i === 0, i === 1];
      }
    }
    b.aim = aimOut; b.fire = fire; b.s1 = f[0]; b.s2 = f[1];
  }

  // 길찾기 이동 방향 (0.18초마다만 다시 계산). 실패하면 fallback 각도
  navTo(b, now, gx, gy, fallback) {
    const ai = b.ai;
    if (now >= ai.navUntil) {
      const a = navAngle(this.map, b.x, b.y, gx, gy);
      ai.navAng = a === null ? fallback : a; ai.navUntil = now + 180;
    }
    return ai.navAng;
  }

  simulate(now, dt, canAct) {
    const ps = this.players;
    for (const p of ps) {
      if (!p.alive) continue;
      const ox = p.x, oy = p.y;   // 이번 틱 시작 위치 (벽 통과 방지용)
      if (p.dash && now < p.dash.until) {
        p.x += p.dash.vx * dt; p.y += p.dash.vy * dt; p.svx = p.svy = 0;
        for (const q of ps) {
          if (!p.dash) break; // 받아치기로 돌진이 끊긴 경우
          if (q === p || !q.alive || p.dash.hit.has(q.id)) continue;
          if (dist2(p, q) < (PR * 2 + 4) ** 2) {
            p.dash.hit.add(q.id);
            this.src = 'dash';
            this.damage(q, 22, p.id, { x: p.x, y: p.y, p: 380 });
          }
        }
      } else {
        p.dash = null;
        let spd = BASE_SPEED * (p.slowUntil > now ? 0.5 : 1) * (p.atkSlowUntil > now ? 0.55 : 1) * (p.speedUntil > now ? PICK.speedMul : 1);
        if (p.stunUntil > now) spd = 0;
        const tvx = p.mx * spd, tvy = p.my * spd;
        const k = 1 - Math.exp(-dt * ((tvx || tvy) ? 40 : 50)); // 키를 누르면 거의 바로 속도가 붙고, 떼면 바로 멈춤
        p.svx = (p.svx || 0) + (tvx - (p.svx || 0)) * k;
        p.svy = (p.svy || 0) + (tvy - (p.svy || 0)) * k;
        p.x += p.svx * dt; p.y += p.svy * dt;
      }
      if (p.kv) {
        if (now < p.kv.until) { p.x += p.kv.vx * dt; p.y += p.kv.vy * dt; } else p.kv = null;
      }
      {   // 서버가 잠깐 멈췄다 돌아와 한 번에 멀리 움직여도 벽을 뚫지 않도록 8px 이하로 나눠서 충돌 처리
        const mdx = p.x - ox, mdy = p.y - oy, mn = Math.min(40, Math.ceil(Math.hypot(mdx, mdy) / 8));
        if (mn > 1) { p.x = ox; p.y = oy; for (let i = 0; i < mn; i++) { p.x += mdx / mn; p.y += mdy / mn; pushOutWalls(p); } }
        else pushOutWalls(p);
      }
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
    if (canAct) {
      for (const p of ps) if (p.alive) this.act(p, now);
      // 자기장 밖 피해
      const z = this.zone(now);
      for (const p of ps) {
        if (!p.alive) continue;
        if (p.x < z[0] || p.x > z[2] || p.y < z[1] || p.y > z[3]) {
          // 자기장이 줄어들기 시작한 뒤 시간이 지날수록 피해가 점점 세짐 (30초마다 +1배, 최대 6배)
          const zt = Math.max(0, (now - this.fightAt) / 1000 - ZONE.delay);
          p.hp -= ZONE.dps * Math.min(6, 1 + zt / 30) * dt;
          if (p.hp <= 0) {
            p.hp = 0; p.alive = false;
            this.ev.push({ k: 'die', x: Math.round(p.x), y: Math.round(p.y) });
            this.ev.push({ k: 'kill', o: 0, v: p.id, s: 'zone' });
          }
        }
      }
    }

    if (canAct) this.updatePickups(now);

    // 투사체 (단검)
    for (let i = this.projs.length - 1; i >= 0; i--) {
      const b = this.projs[i];
      b.x += b.vx * dt; b.y += b.vy * dt; b.life -= dt;
      let remove = false;
      if (b.life <= 0 || b.x < 0 || b.x > W || b.y < 0 || b.y > H || hitsWall(b.x, b.y, b.r)) {
        remove = true;
      } else {
        for (const q of ps) {
          if (!q.alive || q.id === b.owner) continue;
          if (dist2(b, q) < (b.r + PR) ** 2) {
            this.src = 'throw';
            this.damage(q, b.dmg, b.owner, { x: b.x - b.vx * 0.05, y: b.y - b.vy * 0.05, p: 120 });
            remove = true;
            break;
          }
        }
      }
      if (remove) this.projs.splice(i, 1);
    }
  }

  updatePickups(now) {
    for (let i = this.pickups.length - 1; i >= 0; i--) if (now >= this.pickups[i].expire) this.pickups.splice(i, 1);
    if (this.nextPickup && now >= this.nextPickup) {
      if (this.pickups.length < (this.map.pickMax || PICK.max)) this.spawnPickup(now);
      this.nextPickup = now + PICK.every[0] + Math.random() * (PICK.every[1] - PICK.every[0]);
    }
    for (const p of this.players) {
      if (!p.alive) continue;
      for (let i = this.pickups.length - 1; i >= 0; i--) {
        const u = this.pickups[i];
        if (dist2(p, u) < (PR + PICK.r) ** 2) { this.pickups.splice(i, 1); this.applyBuff(p, u.type, now); }
      }
    }
  }
  spawnPickup(now) {
    const z = this.zone(now), m = 90;
    for (let t = 0; t < 40; t++) {
      const x = z[0] + m + Math.random() * Math.max(1, z[2] - z[0] - 2 * m);
      const y = z[1] + m + Math.random() * Math.max(1, z[3] - z[1] - 2 * m);
      if (blocked(x, y, PICK.r + 6)) continue;
      if (this.pickups.some(u => dist2(u, { x, y }) < 250 * 250)) continue;     // 다른 버프와 겹치지 않게
      if (this.players.some(p => p.alive && dist2(p, { x, y }) < 220 * 220)) continue; // 플레이어 바로 앞에 생기지 않게
      let r = Math.random() * BUFF_WEIGHT.reduce((a, b) => a + b, 0), type = 0;
      for (let i = 0; i < BUFF_WEIGHT.length; i++) { r -= BUFF_WEIGHT[i]; if (r <= 0) { type = i; break; } }
      this.pickups.push({ id: this.pid++, type, x: Math.round(x), y: Math.round(y), expire: now + PICK.life });
      this.ev.push({ k: 'pspawn', t: type, x: Math.round(x), y: Math.round(y) });
      return;
    }
  }
  applyBuff(p, type, now) {
    const B = BUFFS[type];
    if (B.id === 'heal') p.hp = Math.min(MAX_HP, p.hp + PICK.healAmt);
    else if (B.id === 'speed') p.speedUntil = now + B.dur;
    else if (B.id === 'power') p.powerUntil = now + B.dur;
    else if (B.id === 'cdr') { p.cd[1] = 0; p.cd[2] = 0; }
    this.ev.push({ k: 'pick', o: p.id, t: type, x: Math.round(p.x), y: Math.round(p.y) });
  }

  act(p, now) {
    if (p.stunUntil > now) return;
    let want = p.fire;
    if (!p.isBot) {
      // 자동 공격: 가장 가까운 적을 바라보고, 사거리 안이면 알아서 벤다
      let t = null, bd = Infinity;
      for (const q of this.players) {
        if (q === p || !q.alive) continue;
        const d2 = dist2(p, q);
        if (d2 < bd) { bd = d2; t = q; }
      }
      if (t) p.aim = Math.atan2(t.y - p.y, t.x - p.x);
      want = !!t && bd <= (ATK.range + PR) ** 2 && !rayBlocked(p.x, p.y, t.x, t.y);
    }
    if (want && now >= p.cd[0]) this.swing(p, now);
    for (let s = 1; s <= 2; s++) {
      const pressed = s === 1 ? p.s1 : p.s2;
      const sid = p.skills[s - 1];
      if (pressed && sid && now >= p.cd[s]) {
        if (this.cast(p, sid, now)) {
          p.cd[s] = now + SKILLS[sid].cd;
          this.ev.push({ k: 'cast', o: p.id, s: sid, x: Math.round(p.x), y: Math.round(p.y), a: +p.aim.toFixed(2) });
        }
      }
    }
  }

  // 기본 공격: 부채꼴 베기. 3타째는 범위/피해/밀치기가 큰 강타
  swing(p, now) {
    p.combo = now <= p.comboUntil ? p.combo + 1 : 1;
    const heavy = p.combo >= 3;
    if (heavy) p.combo = 0;
    p.comboUntil = now + ATK.comboWindow;
    const range = heavy ? ATK.hRange : ATK.range, arc = heavy ? ATK.hArc : ATK.arc;
    const dmg = heavy ? ATK.hDmg : ATK.dmg, kb = heavy ? ATK.hKb : ATK.kb;
    p.cd[0] = now + (heavy ? ATK.hCd : ATK.cd);
    p.atkSlowUntil = now + 220;
    this.src = 'sword';
    const dx = Math.cos(p.aim), dy = Math.sin(p.aim);
    p.kv = { vx: dx * 240, vy: dy * 240, until: now + 110 }; // 베면서 살짝 앞으로 나감
    this.ev.push({ k: 'swing', o: p.id, x: Math.round(p.x), y: Math.round(p.y), a: +p.aim.toFixed(2), r: range + PR, arc, h: heavy ? 1 : 0 });
    for (const q of this.players) {
      if (q === p || !q.alive) continue;
      const d = Math.hypot(q.x - p.x, q.y - p.y);
      if (d > range + PR) continue;
      const diff = Math.abs(angDiff(Math.atan2(q.y - p.y, q.x - p.x), p.aim));
      if (diff > arc / 2 + Math.atan2(PR, Math.max(d, 1))) continue;
      if (rayBlocked(p.x, p.y, q.x, q.y)) continue;
      this.damage(q, dmg, p.id, { x: p.x, y: p.y, p: kb });
    }
  }

  cast(p, sid, now) {
    this.src = sid;
    const dx = Math.cos(p.aim), dy = Math.sin(p.aim);
    const enemies = this.players.filter(q => q !== p && q.alive);
    switch (sid) {
      case 'dash':
        p.dash = { vx: dx * 1500, vy: dy * 1500, until: now + 200, hit: new Set() };
        return true;
      case 'whirl':
        this.ev.push({ k: 'whirl', o: p.id, x: Math.round(p.x), y: Math.round(p.y), r: 95 + PR });
        for (const q of enemies) {
          if (dist2(p, q) < (95 + PR) ** 2 && !rayBlocked(p.x, p.y, q.x, q.y)) this.damage(q, 16, p.id, { x: p.x, y: p.y, p: 280 });
        }
        return true;
      case 'slam':
        this.ev.push({ k: 'slam', o: p.id, x: Math.round(p.x), y: Math.round(p.y), r: 120 + PR });
        for (const q of enemies) {
          if (dist2(p, q) < (120 + PR) ** 2 && !rayBlocked(p.x, p.y, q.x, q.y)) this.damage(q, 20, p.id, { x: p.x, y: p.y, p: 420, stun: 600 });
        }
        return true;
      case 'parry':
        p.parryUntil = now + 450;
        return true;
      case 'shield':
        p.shieldUntil = now + 1800;
        return true;
      case 'blink': {
        let ba = p.aim;
        if (!p.isBot) ba = (p.mx || p.my) ? Math.atan2(p.my, p.mx) : p.aim + Math.PI;
        const bx = Math.cos(ba), by = Math.sin(ba);
        let nx = p.x, ny = p.y;
        for (let d = 6; d <= 220; d += 6) {
          const tx = p.x + bx * d, ty = p.y + by * d;
          if (blocked(tx, ty, PR)) break;
          nx = tx; ny = ty;
        }
        if (nx === p.x && ny === p.y) return false;
        this.ev.push({ k: 'blink', o: p.id, x1: Math.round(p.x), y1: Math.round(p.y), x2: Math.round(nx), y2: Math.round(ny) });
        p.x = nx; p.y = ny;
        return true;
      }
      case 'heal':
        p.hp = Math.min(MAX_HP, p.hp + 30);
        this.ev.push({ k: 'heal', o: p.id, x: Math.round(p.x), y: Math.round(p.y) });
        return true;
      case 'throw':
        this.projs.push({ x: p.x + dx * 24, y: p.y + dy * 24, vx: dx * 900, vy: dy * 900, r: 7, dmg: 14, owner: p.id, life: 0.6, kind: 0 });
        return true;
      case 'nova':
        this.ev.push({ k: 'nova', o: p.id, x: Math.round(p.x), y: Math.round(p.y), r: 150 });
        for (const q of enemies) {
          if (dist2(p, q) < (150 + PR) ** 2) { if (this.damage(q, 10, p.id) && q.alive) q.slowUntil = now + 2500; }
        }
        return true;
      default:
        return false;
    }
  }

  // kb = { x, y, p, stun }: (x, y)에서 멀어지는 방향으로 p만큼 밀어내고, stun(ms)만큼 기절
  knock(q, fx, fy, power) {
    const dx = q.x - fx, dy = q.y - fy, d = Math.hypot(dx, dy) || 1;
    q.kv = { vx: dx / d * power, vy: dy / d * power, until: this.now + 160 };
    q.dash = null;
  }
  damage(q, dmg, ownerId, kb) {
    if (!q.alive) return false;
    const x = Math.round(q.x), y = Math.round(q.y);
    if (q.parryUntil > this.now) {
      // 받아치기 성공: 피해 무효 + 공격자 기절
      q.parryUntil = 0;
      this.ev.push({ k: 'parry', x, y });
      const o = this.players.find(p => p.id === ownerId);
      if (o && o !== q && o.alive) {
        o.stunUntil = Math.max(o.stunUntil, this.now + 1000);
        o.dash = null;
        this.knock(o, q.x, q.y, 260);
      }
      return false;
    }
    if (q.shieldUntil > this.now) { this.ev.push({ k: 'block', x, y }); return false; }
    const ow = this.players.find(pl => pl.id === ownerId);
    if (ow && ow.powerUntil > this.now) dmg = Math.round(dmg * PICK.powerMul);
    q.hp -= dmg;
    this.ev.push({ k: 'hit', x, y });
    if (q.hp <= 0) {
      q.hp = 0; q.alive = false;
      this.ev.push({ k: 'die', x, y });
      this.ev.push({ k: 'kill', o: ownerId, v: q.id, s: this.src || 'sword' });
    } else if (kb) {
      if (kb.p) this.knock(q, kb.x, kb.y, kb.p);
      if (kb.stun) q.stunUntil = Math.max(q.stunUntil, this.now + kb.stun);
    }
    return true;
  }

  snapshot(now) {
    const s = {
      T: now,   // 서버 시각(ms): 클라이언트가 다른 플레이어를 일정한 간격으로 보간해서 그리는 데 사용
      t: 's', ph: this.phase, tm: Math.max(0, this.phaseEnd - now),
      p: this.players.map(p => [
        p.id, Math.round(p.x), Math.round(p.y), +p.aim.toFixed(2), Math.max(0, Math.ceil(p.hp)),
        (p.alive ? 1 : 0) | (p.shieldUntil > now ? 2 : 0) | (p.slowUntil > now ? 4 : 0) | (p.dash && now < p.dash.until ? 8 : 0) |
          (p.stunUntil > now ? 16 : 0) | (p.parryUntil > now ? 32 : 0) | (p.combo >= 2 && now <= p.comboUntil ? 64 : 0) |
          (p.speedUntil > now ? 128 : 0) | (p.powerUntil > now ? 256 : 0) | (p.atkSlowUntil > now ? 512 : 0),
        Math.max(0, Math.ceil(p.cd[1] - now)), Math.max(0, Math.ceil(p.cd[2] - now)),
      ]),
      b: this.projs.map(b => [Math.round(b.x), Math.round(b.y), b.r, b.kind, b.owner, Math.round(b.vx), Math.round(b.vy)]),
      m: [],
      u: this.pickups.map(u => [u.id, u.type, u.x, u.y, Math.max(0, u.expire - now)]),
      z: this.zone(now).map(Math.round),
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
}, 25);

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
