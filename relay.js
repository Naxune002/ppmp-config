// PPMP Relay - room-based UDP relay for the People Playground multiplayer mod.
// Run:  node relay.js            (listens on UDP port 7777)
//
// Every packet starts with 1 byte = message type.
// Control messages carry JSON after the type byte. Game data is raw bytes.
//
// Client -> Relay
//   0x01 HOST   {"name":"Bob","maxPlayers":4}
//   0x02 JOIN   {"code":"K7Q2","name":"Amy"}
//   0x03 DATA   [targetId:1 byte (255 = everyone else)] [payload...]
//   0x04 LEAVE
//   0x05 PING   [anything - echoed back]
//
// Relay -> Client
//   0x81 ROOM_CREATED  {"code":"K7Q2","playerId":0}
//   0x82 JOINED        {"code":"K7Q2","playerId":1,"players":[{"id":0,"name":"Bob"},...]}
//   0x83 ERROR         {"reason":"Room not found"}
//   0x84 PLAYER_JOINED {"id":1,"name":"Amy"}
//   0x85 DATA          [fromId:1 byte] [payload...]
//   0x86 PONG          [same bytes as the ping]
//   0x87 PLAYER_LEFT   {"id":1}
//   0x88 ROOM_CLOSED   {"reason":"Host left"}

const dgram = require("dgram");
const fs = require("fs");
const path = require("path");

const PORT = Number(process.env.PORT) || 7777;

// ---------- Protection limits (public server) ----------
const MAX_PACKET_BYTES = 16 * 1024;     // bigger packets are ignored
const MAX_ROOMS = 500;                  // whole server
const MAX_PLAYERS_TOTAL = 2000;         // whole server
const MAX_ROOMS_PER_IP = 3;             // rooms one internet address can host at once
const MAX_PLAYERS_PER_IP = 8;           // connections from one internet address
const RATE_PACKETS_PER_SEC = 600;       // per connection, with a 2 second burst
const RATE_BYTES_PER_SEC = 600 * 1024;  // per connection, with a 2 second burst
const CONTROL_PER_10S = 20;             // host/join requests per address per 10 s
const FAILED_JOINS_PER_MIN = 15;        // wrong room codes per address per minute (stops code guessing)
const BAN_FILE = path.join(__dirname, "banned.txt"); // one IP per line, # for comments
// Owner file (kept ONLY on the server, never in the public mod): lines of  "IP  Name"
// A player from that IP may use any name they choose; nobody else may use that Name.
const ADMIN_FILE = path.join(__dirname, "admins.txt");
const TIMEOUT_MS = 10000;        // drop players silent for this long
const MAX_PLAYERS_LIMIT = 8;
const CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; // no 0/O/1/I to avoid confusion

const T = {
  HOST: 0x01, JOIN: 0x02, DATA: 0x03, LEAVE: 0x04, PING: 0x05, WHOAMI: 0x06,
  ROOM_CREATED: 0x81, JOINED: 0x82, ERROR: 0x83, PLAYER_JOINED: 0x84,
  RELAY_DATA: 0x85, PONG: 0x86, PLAYER_LEFT: 0x87, ROOM_CLOSED: 0x88, WHOAMI_REPLY: 0x89,
};

const sock = dgram.createSocket("udp4");
const rooms = new Map();    // code -> { code, hostKey, maxPlayers, players: Map<id, player> }
const players = new Map();  // "ip:port" -> { key, address, port, id, name, room, lastSeen }

const keyOf = (r) => `${r.address}:${r.port}`;
const log = (...a) => console.log(new Date().toLocaleTimeString(), ...a);

// ---------- Protection helpers ----------
let banned = new Set();
function loadBans() {
  try {
    const lines = fs.readFileSync(BAN_FILE, "utf8").split(/\r?\n/).map((l) => l.replace(/#.*/, "").trim()).filter(Boolean);
    const next = new Set(lines);
    if (next.size !== banned.size) log(`Ban list: ${next.size} address(es)`);
    banned = next;
  } catch { banned = new Set(); }
}
loadBans();
setInterval(loadBans, 15000); // edit banned.txt while running, it reloads by itself

const ipStats = new Map(); // ip -> { control: [times], failedJoins: [times] }
function ipStat(ip) {
  let s = ipStats.get(ip);
  if (!s) { s = { control: [], failedJoins: [] }; ipStats.set(ip, s); }
  return s;
}
function recent(list, windowMs) {
  const cut = Date.now() - windowMs;
  while (list.length && list[0] < cut) list.shift();
  return list;
}
function countWhere(map, fn) { let n = 0; for (const v of map.values()) if (fn(v)) n++; return n; }

// Token bucket per connection: refills every second, holds up to 2 seconds of traffic
function allowTraffic(p, bytes) {
  const now = Date.now();
  if (!p.bucket) p.bucket = { pk: RATE_PACKETS_PER_SEC * 2, by: RATE_BYTES_PER_SEC * 2, t: now, dropped: 0 };
  const b = p.bucket;
  const dt = (now - b.t) / 1000; b.t = now;
  b.pk = Math.min(RATE_PACKETS_PER_SEC * 2, b.pk + dt * RATE_PACKETS_PER_SEC);
  b.by = Math.min(RATE_BYTES_PER_SEC * 2, b.by + dt * RATE_BYTES_PER_SEC);
  if (b.pk < 1 || b.by < bytes) { b.dropped++; return false; }
  b.pk -= 1; b.by -= bytes;
  return true;
}

const stats = { packets: 0, bytesIn: 0, bytesOut: 0, dropped: 0 };

function send(p, type, body) {
  let payload;
  if (body === undefined) payload = Buffer.alloc(0);
  else if (Buffer.isBuffer(body)) payload = body;
  else payload = Buffer.from(JSON.stringify(body), "utf8");
  const pkt = Buffer.concat([Buffer.from([type]), payload]);
  stats.bytesOut += pkt.length;
  sock.send(pkt, p.port, p.address);
}

function sendTo(rinfo, type, body) { send({ address: rinfo.address, port: rinfo.port }, type, body); }

function parseJson(buf) {
  try { return JSON.parse(buf.toString("utf8")); } catch { return null; }
}

function newCode() {
  let code;
  do {
    code = Array.from({ length: 4 }, () => CODE_CHARS[Math.floor(Math.random() * CODE_CHARS.length)]).join("");
  } while (rooms.has(code));
  return code;
}

function cleanName(n) {
  // letters/numbers in any language, space, _ - .
  return String(n || "").replace(/[^\p{L}\p{N} _\-.]/gu, "").trim().slice(0, 20) || "Player";
}

// ---------- Owner names ----------
let admins = new Map(); // ip -> reserved name ("" if none)
function loadAdmins() {
  try {
    const next = new Map();
    for (const raw of fs.readFileSync(ADMIN_FILE, "utf8").split(/\r?\n/)) {
      const line = raw.replace(/#.*/, "").trim();
      if (!line) continue;
      const [ip, ...rest] = line.split(/\s+/);
      next.set(ip, rest.join(" "));
    }
    if (next.size !== admins.size) log(`Owner list: ${next.size} address(es)`);
    admins = next;
  } catch { admins = new Map(); }
}
loadAdmins();
setInterval(loadAdmins, 15000);
const isAdmin = (ip) => admins.has(ip);
function reservedName(name) {
  const n = name.toLowerCase();
  for (const r of admins.values()) if (r && r.toLowerCase() === n) return true;
  return false;
}
// Pick the name a player is shown as. Normal players get their Steam name;
// the owner may pick any name. Nobody else can take the owner's name.
function decideName(ip, msg) {
  if (isAdmin(ip) && msg?.customName && String(msg.customName).trim()) return cleanName(msg.customName);
  const name = cleanName(msg?.name);
  if (!isAdmin(ip) && reservedName(name)) return "Player";
  return name;
}

function removePlayer(p, reason) {
  const room = p.room;
  players.delete(p.key);
  if (!room) return;
  room.players.delete(p.id);

  if (p.key === room.hostKey) {
    // Host gone -> close the room
    for (const other of room.players.values()) {
      send(other, T.ROOM_CLOSED, { reason: "Host left" });
      players.delete(other.key);
    }
    rooms.delete(room.code);
    log(`Room ${room.code} closed (${reason})`);
  } else {
    for (const other of room.players.values()) send(other, T.PLAYER_LEFT, { id: p.id });
    log(`${p.name} left room ${room.code} (${reason})`);
  }
}

function handleHost(rinfo, msg) {
  const key = keyOf(rinfo);
  const existing = players.get(key);
  if (existing && existing.room && existing.room.hostKey === key) {
    // Repeated host request (UDP resend) - answer again instead of making a new room
    return send(existing, T.ROOM_CREATED, { code: existing.room.code, playerId: 0, maxPlayers: existing.room.maxPlayers, name: existing.name });
  }
  if (existing) removePlayer(existing, "re-hosting");
  if (rooms.size >= MAX_ROOMS) return sendTo(rinfo, T.ERROR, { reason: "Server is full, try again later" });
  if (players.size >= MAX_PLAYERS_TOTAL) return sendTo(rinfo, T.ERROR, { reason: "Server is full, try again later" });
  if (countWhere(rooms, (r) => r.hostKey.split(":")[0] === rinfo.address) >= MAX_ROOMS_PER_IP)
    return sendTo(rinfo, T.ERROR, { reason: "Too many rooms from your connection" });
  if (countWhere(players, (x) => x.address === rinfo.address) >= MAX_PLAYERS_PER_IP)
    return sendTo(rinfo, T.ERROR, { reason: "Too many connections from your address" });

  const max = Math.max(2, Math.min(MAX_PLAYERS_LIMIT, Number(msg?.maxPlayers) || 4));
  const code = newCode();
  const p = { key, address: rinfo.address, port: rinfo.port, id: 0, name: decideName(rinfo.address, msg), room: null, lastSeen: Date.now() };
  const room = { code, hostKey: key, maxPlayers: max, players: new Map([[0, p]]) };
  p.room = room;
  rooms.set(code, room);
  players.set(key, p);

  send(p, T.ROOM_CREATED, { code, playerId: 0, maxPlayers: max, name: p.name });
  log(`${p.name} hosted room ${code} (max ${max})`);
}

function handleJoin(rinfo, msg) {
  const key = keyOf(rinfo);
  const code = String(msg?.code || "").toUpperCase().trim();
  const room = rooms.get(code);
  if (!room) {
    ipStat(rinfo.address).failedJoins.push(Date.now());
    return sendTo(rinfo, T.ERROR, { reason: "Room not found" });
  }

  const existing = players.get(key);
  if (existing && existing.room === room) {
    // Duplicate join packet (UDP can repeat) - just resend the answer
    return send(existing, T.JOINED, joinedBody(room, existing));
  }
  if (existing) removePlayer(existing, "joined another room");
  if (room.players.size >= room.maxPlayers) return sendTo(rinfo, T.ERROR, { reason: "Room is full" });
  if (players.size >= MAX_PLAYERS_TOTAL) return sendTo(rinfo, T.ERROR, { reason: "Server is full, try again later" });
  if (countWhere(players, (x) => x.address === rinfo.address) >= MAX_PLAYERS_PER_IP)
    return sendTo(rinfo, T.ERROR, { reason: "Too many connections from your address" });

  let id = 1;
  while (room.players.has(id)) id++;
  const p = { key, address: rinfo.address, port: rinfo.port, id, name: decideName(rinfo.address, msg), room, lastSeen: Date.now() };
  room.players.set(id, p);
  players.set(key, p);

  send(p, T.JOINED, joinedBody(room, p));
  for (const other of room.players.values()) {
    if (other !== p) send(other, T.PLAYER_JOINED, { id: p.id, name: p.name });
  }
  log(`${p.name} joined room ${code} as player ${id}`);
}

function joinedBody(room, p) {
  return {
    code: room.code,
    playerId: p.id,
    name: p.name,
    players: [...room.players.values()].map((x) => ({ id: x.id, name: x.name })),
  };
}

function handleData(p, buf) {
  if (!p || !p.room || buf.length < 1) return;
  const target = buf[0];
  if (!allowTraffic(p, buf.length)) { stats.dropped++; return; }
  const out = Buffer.concat([Buffer.from([T.RELAY_DATA, p.id]), buf.subarray(1)]);
  for (const other of p.room.players.values()) {
    if (other === p) continue;
    if (target === 255 || target === other.id) { stats.bytesOut += out.length; sock.send(out, other.port, other.address); }
  }
}

sock.on("message", (data, rinfo) => {
  stats.packets++; stats.bytesIn += data.length;
  if (data.length < 1 || data.length > MAX_PACKET_BYTES) return;
  if (banned.has(rinfo.address)) return;
  const type = data[0];
  const body = data.subarray(1);
  const p = players.get(keyOf(rinfo));
  if (p) p.lastSeen = Date.now();

  try {
    switch (type) {
      case T.HOST:
      case T.JOIN: {
        const st = ipStat(rinfo.address);
        if (recent(st.control, 10000).length >= CONTROL_PER_10S) return; // spamming requests: ignore
        st.control.push(Date.now());
        if (type === T.JOIN && recent(st.failedJoins, 60000).length >= FAILED_JOINS_PER_MIN)
          return sendTo(rinfo, T.ERROR, { reason: "Too many wrong codes, wait a minute" });
        if (body.length > 512) return;
        return type === T.HOST ? handleHost(rinfo, parseJson(body)) : handleJoin(rinfo, parseJson(body));
      }
      case T.WHOAMI: {
        const st = ipStat(rinfo.address);
        if (recent(st.control, 10000).length >= CONTROL_PER_10S) return;
        st.control.push(Date.now());
        return sendTo(rinfo, T.WHOAMI_REPLY, { admin: isAdmin(rinfo.address) });
      }
      case T.DATA:  return handleData(p, body);
      case T.LEAVE: if (p) removePlayer(p, "left"); return;
      case T.PING:
        // Small pings only, rate limited per address (answers are the same size, so no flooding through us)
        if (body.length > 64) return;
        if (!allowTraffic(p || ipStat(rinfo.address), data.length)) return;
        return sendTo(rinfo, T.PONG, body);
    }
  } catch (e) {
    console.error("Error handling packet:", e.message); // never let one bad packet crash the server
  }
});

// Drop players that went silent (crashed, lost connection)
setInterval(() => {
  const now = Date.now();
  for (const p of [...players.values()]) {
    if (now - p.lastSeen > TIMEOUT_MS) removePlayer(p, "timed out");
  }
}, 1000);

// Forget old per-address counters
setInterval(() => {
  for (const [ip, st] of ipStats) {
    recent(st.control, 10000); recent(st.failedJoins, 60000);
    if (!st.control.length && !st.failedJoins.length) ipStats.delete(ip);
  }
}, 60000);

// Status line every 60s
setInterval(() => {
  const mb = (n) => (n / 1048576).toFixed(1);
  log(`Status: ${rooms.size} room(s), ${players.size} player(s), last minute: in ${mb(stats.bytesIn)} MB, out ${mb(stats.bytesOut)} MB, dropped ${stats.dropped} (rate limit)`);
  stats.packets = 0; stats.bytesIn = 0; stats.bytesOut = 0; stats.dropped = 0;
}, 60000);

process.on("uncaughtException", (e) => console.error("Unexpected error (server keeps running):", e));

sock.on("error", (e) => { console.error("Socket error:", e.message); });
sock.bind(PORT, () => log(`PPMP relay listening on UDP port ${PORT}`));
