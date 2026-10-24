// =====================================================================
// STORMFALL  -  authoritative game server  (STAGE 1: movement + connecting players)
// Run:  npm install && npm start      (then open http://localhost:3000)
//
// Design:
//  * Clients send ONLY inputs ("commands"). Each command = one 1/60s step of input.
//  * The server runs the same movement code as the client (shared block below),
//    owns every player's true position, and broadcasts snapshots at 20 Hz.
//  * Anti-cheat: a per-player "time budget" means a client can never simulate more
//    movement than real time allows (stops speed hacks / command flooding).
// =====================================================================
"use strict";

const http = require("http");
const fs = require("fs");
const path = require("path");
const { WebSocketServer } = require("ws");

const PORT = process.env.PORT || 3000;
const TICK_RATE = 20;                 // snapshots per second
const TICK_MS = 1000 / TICK_RATE;
const MAX_PLAYERS = 16;

// ===================== SHARED CODE =====================================
// This block MUST be identical in server.js and index.html so that the
// client's prediction matches the server's simulation exactly.
// SHARED-BEGIN
const WORLD_HALF = 150;               // map is a square from -150 to +150
const TICK_DT = 1 / 60;               // fixed physics step (one command = one step)
const EPS = 0.001;
const MOVE = {
  walk: 5, sprint: 8.5, crouch: 2.5,  // metres / second
  jump: 7.5, gravity: 22,
  radius: 0.4, stand: 1.8, crouchH: 1.2,
  eyeStand: 1.62, eyeCrouch: 1.1
};

// Small deterministic PRNG: same seed -> same map on server and clients.
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Builds the whole map as axis-aligned boxes. Only the seed is sent over the network.
//  boxes    = solid colliders (most are also drawn; "hidden" ones are drawn differently)
//  deco     = visual-only boxes (floors)
//  trees / rocks = extra info the client uses to draw nicer shapes
//  loot     = spots inside buildings where items will spawn (used in a later stage)
function generateMap(seed) {
  const rnd = mulberry32(seed);
  const R = (a, b) => a + rnd() * (b - a);
  const boxes = [], deco = [], trees = [], rocks = [], buildings = [], loot = [];
  const addBox = (cx, cy, cz, sx, sy, sz, col, hidden) => boxes.push({
    x0: cx - sx / 2, y0: cy - sy / 2, z0: cz - sz / 2,
    x1: cx + sx / 2, y1: cy + sy / 2, z1: cz + sz / 2, col: col, hidden: !!hidden
  });
  const T = 0.4, H = 3.4, DOOR_W = 2.4, DOOR_H = 2.6;

  // One wall of a building. isX=true -> runs along X at z=fixed. door = offset of door centre or null.
  const wall = (isX, fixed, c, len, door, col) => {
    const seg = (a0, a1, y0, y1) => {
      if (a1 - a0 < 0.01) return;
      const mid = (a0 + a1) / 2, l = a1 - a0, hy = (y0 + y1) / 2, sy = y1 - y0;
      if (isX) addBox(mid, hy, fixed, l, sy, T, col); else addBox(fixed, hy, mid, T, sy, l, col);
    };
    const a0 = c - len / 2, a1 = c + len / 2;
    if (door === null) seg(a0, a1, 0, H);
    else {
      const g0 = c + door - DOOR_W / 2, g1 = c + door + DOOR_W / 2;
      seg(a0, g0, 0, H);            // wall left of door
      seg(g1, a1, 0, H);            // wall right of door
      seg(g0, g1, DOOR_H, H);       // lintel above door
    }
  };

  // ---- Buildings on a jittered grid (each has a door, roof, cover crates, loot spots)
  for (let gx = -3; gx <= 3; gx++) for (let gz = -3; gz <= 3; gz++) {
    if (rnd() < 0.5) continue;
    const w = R(10, 17), d = R(10, 16);
    const cx = gx * 40 + R(-8, 8), cz = gz * 40 + R(-8, 8);
    const col = Math.floor(rnd() * 3);
    const doorSide = Math.floor(rnd() * 4);               // 0=N(-z) 1=S(+z) 2=E(+x) 3=W(-x)
    const mx = w / 2 - DOOR_W / 2 - 1, mz = d / 2 - DOOR_W / 2 - 1;
    const oN = R(-mx, mx), oS = R(-mx, mx), oE = R(-mz, mz), oW = R(-mz, mz);
    wall(true, cz - d / 2, cx, w, doorSide === 0 ? oN : null, col);
    wall(true, cz + d / 2, cx, w, doorSide === 1 ? oS : null, col);
    wall(false, cx + w / 2, cz, d, doorSide === 2 ? oE : null, col);
    wall(false, cx - w / 2, cz, d, doorSide === 3 ? oW : null, col);
    addBox(cx, H + 0.15, cz, w + 0.6, 0.3, d + 0.6, 3);   // roof slab
    deco.push({ cx: cx, cy: 0.03, cz: cz, sx: w, sy: 0.06, sz: d, col: 6 });  // floor (visual)
    // two crates in the corners on the side opposite the door
    const c1 = R(0.9, 1.3), c2 = R(0.9, 1.3);
    if (doorSide < 2) {
      const sz = doorSide === 0 ? 1 : -1;
      addBox(cx - (w / 2 - 1.6), c1 / 2, cz + sz * (d / 2 - 1.6), c1, c1, c1, 4);
      addBox(cx + (w / 2 - 1.6), c2 / 2, cz + sz * (d / 2 - 1.6), c2, c2, c2, 4);
    } else {
      const sx = doorSide === 2 ? -1 : 1;
      addBox(cx + sx * (w / 2 - 1.6), c1 / 2, cz - (d / 2 - 1.6), c1, c1, c1, 4);
      addBox(cx + sx * (w / 2 - 1.6), c2 / 2, cz + (d / 2 - 1.6), c2, c2, c2, 4);
    }
    for (let i = 0; i < 3; i++)
      loot.push({ x: cx + R(-(w / 2 - 2.8), w / 2 - 2.8), z: cz + R(-(d / 2 - 2.8), d / 2 - 2.8) });
    buildings.push({ cx: cx, cz: cz, w: w, d: d, h: H, doorSide: doorSide });
  }
  const nearBuilding = (x, z, m) =>
    buildings.some(b => Math.abs(x - b.cx) < b.w / 2 + m && Math.abs(z - b.cz) < b.d / 2 + m);

  // ---- Outdoor cover: crates and low concrete walls
  for (let i = 0; i < 70; i++) {
    const x = R(-140, 140), z = R(-140, 140), kind = rnd(), s = R(1, 1.6), L = R(3, 6), alongX = rnd() < 0.5;
    if (nearBuilding(x, z, 3)) continue;
    if (kind < 0.5) addBox(x, s / 2, z, s, s, s, 4);
    else addBox(x, 0.6, z, alongX ? L : 0.5, 1.2, alongX ? 0.5 : L, 7);
  }
  // ---- Trees (square trunk collider; foliage is visual only)
  for (let i = 0; i < 170; i++) {
    const x = R(-146, 146), z = R(-146, 146), s = R(0.8, 1.5);
    if (nearBuilding(x, z, 4)) continue;
    addBox(x, 2.5 * s, z, 0.6 * s, 5 * s, 0.6 * s, 5);
    trees.push({ x: x, z: z, s: s });
  }
  // ---- Rocks (box collider hidden; client draws a low-poly boulder)
  for (let i = 0; i < 40; i++) {
    const x = R(-145, 145), z = R(-145, 145), r = R(1, 2.6), rot = R(0, 6.28);
    if (nearBuilding(x, z, 3)) continue;
    addBox(x, 0.6 * r, z, 1.5 * r, 1.2 * r, 1.5 * r, 7, true);
    rocks.push({ x: x, z: z, r: r, rot: rot });
  }
  return { seed: seed, boxes: boxes, deco: deco, trees: trees, rocks: rocks, buildings: buildings, loot: loot };
}

function boxOverlap(b, x, y, z, h, r) {
  return x + r > b.x0 && x - r < b.x1 && z + r > b.z0 && z - r < b.z1 && y + h > b.y0 && y < b.y1;
}
function overlaps(map, x, y, z, h) {
  for (let i = 0; i < map.boxes.length; i++) if (boxOverlap(map.boxes[i], x, y, z, h, MOVE.radius)) return true;
  return false;
}

// One fixed physics step. s = {x,y,z,vx,vy,vz,og,crouch}; cmd = {f,r,k,y,p}
//   f/r = forward/right (-1..1), k = bit flags (1 jump, 2 sprint, 4 crouch), y = yaw
function stepPlayer(map, s, cmd) {
  const dt = TICK_DT, rad = MOVE.radius, boxes = map.boxes;
  // Crouch: can only stand up if there is headroom.
  if (cmd.k & 4) s.crouch = true;
  else if (s.crouch && !overlaps(map, s.x, s.y, s.z, MOVE.stand)) s.crouch = false;
  const h = s.crouch ? MOVE.crouchH : MOVE.stand;

  // Wish direction from input (clamped, so a cheater can't send f=100)
  let f = Math.max(-1, Math.min(1, cmd.f)), rt = Math.max(-1, Math.min(1, cmd.r));
  const len = Math.hypot(f, rt);
  if (len > 1) { f /= len; rt /= len; }
  const sy = Math.sin(cmd.y), cy = Math.cos(cmd.y);
  const wx = -sy * f + cy * rt, wz = -cy * f - sy * rt;
  const speed = s.crouch ? MOVE.crouch : ((cmd.k & 2) && f > 0.1 ? MOVE.sprint : MOVE.walk);

  // Accelerate toward the wish velocity (snappy on ground, floaty in the air)
  const a = Math.min(1, (s.og ? 14 : 2.5) * dt);
  s.vx += (wx * speed - s.vx) * a;
  s.vz += (wz * speed - s.vz) * a;
  if ((cmd.k & 1) && s.og && !s.crouch) { s.vy = MOVE.jump; s.og = false; }
  s.vy -= MOVE.gravity * dt;

  // Move one axis at a time and push out of any box we overlap (simple, robust).
  s.x += s.vx * dt;
  for (let i = 0; i < boxes.length; i++) {
    const b = boxes[i];
    if (boxOverlap(b, s.x, s.y, s.z, h, rad)) {
      if (s.vx > 0) s.x = b.x0 - rad - EPS; else if (s.vx < 0) s.x = b.x1 + rad + EPS;
      s.vx = 0;
    }
  }
  s.z += s.vz * dt;
  for (let i = 0; i < boxes.length; i++) {
    const b = boxes[i];
    if (boxOverlap(b, s.x, s.y, s.z, h, rad)) {
      if (s.vz > 0) s.z = b.z0 - rad - EPS; else if (s.vz < 0) s.z = b.z1 + rad + EPS;
      s.vz = 0;
    }
  }
  s.y += s.vy * dt;
  s.og = false;
  if (s.y <= 0) { s.y = 0; s.vy = 0; s.og = true; }        // flat ground at y=0
  for (let i = 0; i < boxes.length; i++) {
    const b = boxes[i];
    if (boxOverlap(b, s.x, s.y, s.z, h, rad)) {
      if (s.vy <= 0) { s.y = b.y1; s.vy = 0; s.og = true; }   // land on top of a box
      else { s.y = b.y0 - h - EPS; s.vy = 0; }                // bonk head
    }
  }
  // Keep inside the world
  const lim = WORLD_HALF - rad;
  s.x = Math.max(-lim, Math.min(lim, s.x));
  s.z = Math.max(-lim, Math.min(lim, s.z));
}
// SHARED-END
// =======================================================================

// ---------------------------- HTTP server ----------------------------
// The same port serves index.html, so friends only need one link.
const INDEX_PATH = path.join(__dirname, "index.html");
const httpServer = http.createServer((req, res) => {
  const url = req.url.split("?")[0];
  if (url === "/" || url === "/index.html") {
    fs.readFile(INDEX_PATH, (err, data) => {
      if (err) { res.writeHead(500); res.end("index.html not found next to server.js"); return; }
      res.writeHead(200, { "Content-Type": "text/html; charset=utf-8", "Cache-Control": "no-cache" });
      res.end(data);
    });
  } else if (url === "/health") {
    res.writeHead(200); res.end("ok");
  } else {
    res.writeHead(404); res.end("not found");
  }
});
const wss = new WebSocketServer({ server: httpServer, maxPayload: 8 * 1024 });

// ---------------------------- Game state ----------------------------
const MAP_SEED = (Math.random() * 2147483647) | 0;
const map = generateMap(MAP_SEED);
const players = new Map();            // id -> player
let nextId = 1;

const r2 = n => Math.round(n * 100) / 100;
const r3 = n => Math.round(n * 1000) / 1000;
const r4 = n => Math.round(n * 10000) / 10000;
const num = v => (typeof v === "number" && Number.isFinite(v) ? v : 0);

function send(ws, obj) { if (ws.readyState === 1) ws.send(JSON.stringify(obj)); }
function broadcast(obj, exceptId) {
  const msg = JSON.stringify(obj);
  for (const p of players.values()) if (p.id !== exceptId && p.ws.readyState === 1) p.ws.send(msg);
}

// Find a random spot that is not inside a wall/tree/rock.
function pickSpawn() {
  for (let i = 0; i < 60; i++) {
    const x = (Math.random() * 2 - 1) * (WORLD_HALF - 10), z = (Math.random() * 2 - 1) * (WORLD_HALF - 10);
    if (!overlaps(map, x, 0, z, MOVE.stand + 0.2)) return { x: x, z: z };
  }
  return { x: 0, z: 0 };
}
const stateArr = s => [r4(s.x), r4(s.y), r4(s.z), r4(s.vx), r4(s.vy), r4(s.vz), s.og ? 1 : 0, s.crouch ? 1 : 0];

// ---------------------------- Connections ----------------------------
wss.on("connection", (ws) => {
  ws.isAlive = true;
  ws.on("pong", () => { ws.isAlive = true; });
  let player = null;
  let msgCount = 0;
  const rateTimer = setInterval(() => { msgCount = 0; }, 1000);

  ws.on("message", (data) => {
    // Basic flood protection: >200 messages/second gets you disconnected.
    if (++msgCount > 200) { ws.close(1008, "rate limit"); return; }
    let m;
    try { m = JSON.parse(data); } catch (e) { return; }
    if (!m || typeof m !== "object") return;

    if (m.t === "join" && !player) {
      if (players.size >= MAX_PLAYERS) { send(ws, { t: "full" }); ws.close(); return; }
      const id = nextId++;
      let name = String(m.name || "").replace(/[^\w \-.]/g, "").trim().slice(0, 16);
      if (!name) name = "Player" + id;
      const sp = pickSpawn();
      player = {
        id: id, name: name, ws: ws,
        s: { x: sp.x, y: 0, z: sp.z, vx: 0, vy: 0, vz: 0, og: true, crouch: false },
        yaw: Math.random() * Math.PI * 2, pitch: 0,
        lastSeq: 0,          // last command we processed (acked to the client)
        lastQueued: 0,       // last command we accepted into the queue
        queue: [],
        budget: 0.2,         // seconds of movement this player may still simulate
        lastTick: Date.now(),
        dropped: 0, dropWindow: Date.now()
      };
      players.set(id, player);
      send(ws, {
        t: "welcome", id: id, seed: MAP_SEED, tickRate: TICK_RATE,
        me: stateArr(player.s), yaw: player.yaw,
        players: [...players.values()].filter(p => p.id !== id).map(p => ({ id: p.id, name: p.name }))
      });
      broadcast({ t: "join", id: id, name: name }, id);
      console.log("+ " + name + " (#" + id + ")  players=" + players.size);
    }
    else if (m.t === "in" && player) {
      // Input batch: [[seq, forward, right, flags, yaw, pitch], ...]
      const cmds = Array.isArray(m.c) ? m.c.slice(0, 30) : [];
      for (const c of cmds) {
        if (!Array.isArray(c) || c.length < 6) continue;
        const seq = c[0] | 0;
        if (seq <= player.lastQueued) continue;            // ignore replays / old commands
        player.lastQueued = seq;
        player.queue.push({
          seq: seq, f: num(c[1]), r: num(c[2]), k: c[3] | 0,
          y: num(c[4]), p: Math.max(-1.55, Math.min(1.55, num(c[5])))
        });
      }
      while (player.queue.length > 60) player.queue.shift();   // never let the queue grow unbounded
    }
    else if (m.t === "ping") {
      send(ws, { t: "pong", c: num(m.c) });
    }
  });

  ws.on("close", () => {
    clearInterval(rateTimer);
    if (player) {
      players.delete(player.id);
      broadcast({ t: "leave", id: player.id });
      console.log("- " + player.name + " (#" + player.id + ")  players=" + players.size);
    }
  });
  ws.on("error", () => { /* ignore socket errors; 'close' handles cleanup */ });
});

// ---------------------------- Main tick (20 Hz) ----------------------------
function tick() {
  const now = Date.now();

  // 1) Simulate queued inputs for every player
  for (const p of players.values()) {
    const dt = Math.min((now - p.lastTick) / 1000, 0.5);
    p.lastTick = now;
    // ANTI-CHEAT (speed hack): a player earns real elapsed time as "budget"
    // (+5% slack for jitter). Every command costs 1/60 s. No budget = command ignored.
    p.budget = Math.min(p.budget + dt * 1.05, 0.4);
    while (p.queue.length) {
      const c = p.queue.shift();
      p.lastSeq = c.seq;
      if (p.budget < TICK_DT) {
        p.dropped++;
        continue;
      }
      p.budget -= TICK_DT;
      p.yaw = c.y; p.pitch = c.p;
      stepPlayer(map, p.s, c);                         // authoritative movement
      // Position validation: if anything ever produced NaN/huge values, reset safely.
      const s = p.s;
      if (!Number.isFinite(s.x + s.y + s.z) || Math.abs(s.x) > 1000 || Math.abs(s.z) > 1000 || s.y < -5 || s.y > 200) {
        const sp = pickSpawn(); s.x = sp.x; s.y = 0; s.z = sp.z; s.vx = s.vy = s.vz = 0; s.og = true;
      }
    }
    // Kick persistent offenders (hundreds of over-budget commands within 10 s)
    if (now - p.dropWindow > 10000) { p.dropped = 0; p.dropWindow = now; }
    if (p.dropped > 600) { console.log("kick (speed hack?): " + p.name); p.ws.close(1008, "cheating"); }
  }

  // 2) Build one entry per player, then send each client a snapshot without itself
  const entries = [];
  for (const p of players.values()) {
    entries.push([p.id, r2(p.s.x), r2(p.s.y), r2(p.s.z), r3(p.yaw), r3(p.pitch), (p.s.crouch ? 1 : 0) | (p.s.og ? 2 : 0)]);
  }
  for (const p of players.values()) {
    send(p.ws, {
      t: "s", n: now,                                  // n = server time (for interpolation)
      a: p.lastSeq,                                    // a = last input we processed (for reconciliation)
      me: stateArr(p.s),                               // full authoritative state for the receiver
      p: entries.filter(e => e[0] !== p.id)
    });
  }
}

// Drift-corrected loop (keeps a steady 20 Hz even if one tick runs late)
let nextTick = Date.now();
(function loop() {
  tick();
  nextTick += TICK_MS;
  const now = Date.now();
  if (nextTick < now - 1000) nextTick = now;
  setTimeout(loop, Math.max(0, nextTick - now));
})();

// Drop dead connections (closed laptops, dropped wifi) every 10 s
setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    ws.ping();
  }
}, 10000);

httpServer.listen(PORT, () => {
  console.log("STORMFALL server running:  http://localhost:" + PORT + "   (map seed " + MAP_SEED + ")");
});
process.on("SIGTERM", () => { wss.close(); httpServer.close(() => process.exit(0)); });
