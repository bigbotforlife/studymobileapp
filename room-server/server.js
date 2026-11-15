// Room server: creates 4-letter rooms and relays messages between the host and the players who join.
// No dependencies. Run with: node server.js   (PORT env var sets the port, default 3000)
"use strict";
const http = require("http");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");

const PORT = process.env.PORT || 3000;
const GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
const MAX_ROOMS = 5000, MAX_PAYLOAD = 256 * 1024, ROOM_SLOTS = 4;
const CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ";
// Username filter: strips look-alike characters, then checks banned words inside the name and as whole words.
const NAME_INSIDE = ["fuck", "shit", "bitch", "cunt", "nigg", "whore", "slut", "asshole", "dumbass", "bastard", "pussy", "penis", "vagina", "blowjob", "handjob", "cumshot", "jizz", "hentai", "molest", "pedophile", "paedophile", "retard", "faggot", "tranny", "wetback", "hitler", "dildo", "vibrator", "masturbat", "orgasm", "genital", "boob", "cocksuck", "anus", "porno"];
const NAME_WHOLE = ["ass", "arse", "tit", "tits", "dick", "cock", "piss", "fag", "rape", "raped", "rapist", "rapists", "nazi", "pedo", "spic", "kike", "coon", "dyke", "gook", "chink", "negro", "cum", "sex", "boner", "anal", "nude", "nudes", "kkk", "horny", "milf", "orgy", "incest", "wank", "wanker", "twat", "bollock", "bollocks", "porn", "xxx", "nsfw", "hoe", "thot", "cuck", "simp"];
const NAME_OK = ["scunthorpe", "penistone", "analyst", "analysis", "shiitake", "therapist"];
const NAME_RE_IN = NAME_INSIDE.map(w => new RegExp(w.split("").map(c => c + "+").join("")));
const NAME_RE_WH = NAME_WHOLE.map(w => new RegExp("^" + w.split("").map(c => c + "+").join("") + "$"));
function nameBlocked(raw) {
  const base = String(raw || "").normalize("NFKD").replace(/[̀-ͯ]/g, "").toLowerCase();
  const maps = [{ "0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a", "$": "s", "!": "i", "+": "t", "8": "b" }, { "0": "o", "1": "l", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a", "$": "s", "!": "l", "+": "t", "8": "b" }];
  for (const m of maps) {
    const s = base.replace(/[0-9@$!+]/g, c => m[c] || c);
    const tokens = s.split(/[^a-z]+/).filter(Boolean);
    let joined = tokens.join("");
    NAME_OK.forEach(w => { joined = joined.split(w).join(""); });
    if (NAME_RE_IN.some(re => re.test(joined))) return true;
    if (NAME_RE_WH.some(re => re.test(joined) || tokens.some(t => re.test(t)))) return true;
  }
  return false;
}
const rooms = new Map();
function cleanName(s) {
  s = String(s || "").replace(/[\u0000-\u001f\u007f<>&"'`\\]/g, "").replace(/\s+/g, " ").trim().slice(0, 16);
  return s;
}
const allConns = new Set();
const SPORTS = ["volleyball", "badminton", "basketball"];

// ---------- tiny WebSocket implementation (RFC 6455, text frames) ----------
class Conn {
  constructor(socket, ip) {
    this.socket = socket; this.ip = ip; this.buf = Buffer.alloc(0); this.alive = true;
    this.room = null; this.slot = -1; this.frag = null; this.last = Date.now();
    this.msgCount = 0; this.msgWindow = Date.now(); allConns.add(this);
    socket.on("data", d => this.onData(d));
    socket.on("close", () => this.onClose());
    socket.on("error", () => this.onClose());
    socket.setNoDelay(true);
  }
  onData(d) {
    this.buf = Buffer.concat([this.buf, d]);
    if (this.buf.length > MAX_PAYLOAD * 2) return this.kill();
    for (;;) {
      const b = this.buf;
      if (b.length < 2) return;
      const fin = (b[0] & 0x80) !== 0, op = b[0] & 0x0f, masked = (b[1] & 0x80) !== 0;
      let len = b[1] & 0x7f, off = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (b.length < 10) return; const hi = b.readUInt32BE(2); if (hi) return this.kill(); len = b.readUInt32BE(6); off = 10; }
      if (!masked || len > MAX_PAYLOAD) return this.kill();
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4), data = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) data[i] ^= mask[i & 3];
      this.buf = b.subarray(off + 4 + len);
      this.frame(fin, op, data);
      if (!this.alive) return;
    }
  }
  frame(fin, op, data) {
    this.last = Date.now();
    if (op === 0x8) { this.send(Buffer.alloc(0), 0x8); return this.kill(); }
    if (op === 0x9) return this.send(data, 0xA);
    if (op === 0xA) return;
    if (op === 0x1 || op === 0x0) {
      if (op === 0x1) this.frag = [];
      if (!this.frag) return this.kill();
      this.frag.push(data);
      if (Buffer.concat(this.frag).length > MAX_PAYLOAD) return this.kill();
      if (fin) { const s = Buffer.concat(this.frag).toString("utf8"); this.frag = null; this.onText(s); }
    }
  }
  send(payload, op = 0x1) {
    if (!this.alive) return false;
    const p = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
    let head;
    if (p.length < 126) head = Buffer.from([0x80 | op, p.length]);
    else if (p.length < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(p.length, 2); }
    else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeUInt32BE(p.length, 6); }
    try { this.socket.write(Buffer.concat([head, p])); return true; } catch (e) { this.kill(); return false; }
  }
  json(o) { return this.send(JSON.stringify(o)); }
  backlog() { return this.socket.writableLength || 0; }
  kill() { if (!this.alive) return; try { this.socket.destroy(); } catch (e) {} this.onClose(); }
  onClose() { if (!this.alive) return; this.alive = false; allConns.delete(this); leave(this); }
  onText(s) {
    const now = Date.now();
    if (now - this.msgWindow > 1000) { this.msgWindow = now; this.msgCount = 0; }
    if (++this.msgCount > 200) return this.kill();
    let m; try { m = JSON.parse(s); } catch (e) { return; }
    if (!m || typeof m !== "object") return;
    handle(this, m);
  }
}

// ---------- rooms ----------
function newCode() {
  for (let tries = 0; tries < 200; tries++) {
    let c = ""; for (let i = 0; i < 4; i++) c += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!rooms.has(c)) return c;
  }
  return null;
}
function leave(c) {
  const r = c.room; if (!r) return;
  c.room = null;
  if (c.slot === 0) {
    rooms.delete(r.code);
    r.slots.forEach((g, i) => { if (g && i > 0) { g.room = null; g.json({ t: "closed" }); } });
  } else {
    r.slots[c.slot] = null;
    if (r.slots[0]) r.slots[0].json({ t: "left", slot: c.slot });
  }
}
function handle(c, m) {
  if (m.t === "create") {
    if (c.room) return;
    if (rooms.size >= MAX_ROOMS) return c.json({ t: "err", m: "Server is busy, try again soon." });
    const code = newCode(); if (!code) return c.json({ t: "err", m: "Could not make a room." });
    c.name = cleanName(m.name) || "Player";
    if (nameBlocked(c.name)) return c.json({ t: "err", m: "That username is not allowed. Please choose another." });
    const r = { code, slots: new Array(ROOM_SLOTS).fill(null), locked: false, made: Date.now(), pub: false, mode: 1, sport: "volleyball" };
    r.slots[0] = c; c.room = r; c.slot = 0; rooms.set(code, r);
    return c.json({ t: "created", code, slot: 0 });
  }
  if (m.t === "join") {
    if (c.room) return;
    const r = rooms.get(String(m.code || "").toUpperCase().slice(0, 4));
    if (!r) return c.json({ t: "err", m: "Room not found. Check the code." });
    if (r.locked) return c.json({ t: "err", m: "That match has already started." });
    const slot = r.slots.findIndex((s, i) => i > 0 && !s);
    if (slot < 0) return c.json({ t: "err", m: "That room is full." });
    c.name = cleanName(m.name) || "Player";
    if (nameBlocked(c.name)) return c.json({ t: "err", m: "That username is not allowed. Please choose another." });
    r.slots[slot] = c; c.room = r; c.slot = slot;
    c.json({ t: "joined", code: r.code, slot });
    r.slots[0].json({ t: "join", slot, name: c.name });
    return;
  }
  if (m.t === "list" && !c.room) {
    const now = Date.now();
    if (c.lastList && now - c.lastList < 2000) return;
    c.lastList = now;
    const out = [];
    rooms.forEach(r => {
      const n = r.slots.filter(Boolean).length, need = r.mode === 2 ? 4 : 2;
      if (r.pub && !r.locked && n < need) out.push({ code: r.code, host: r.slots[0] ? r.slots[0].name : "", sport: r.sport, mode: r.mode, n, need, made: r.made });
    });
    out.sort((a, b) => b.made - a.made);
    return c.json({ t: "rooms", rooms: out.slice(0, 30) });
  }
  const r = c.room; if (!r) return;
  if (m.t === "meta" && c.slot === 0) {
    r.pub = !!m.pub; r.mode = m.mode === 2 ? 2 : 1; r.sport = SPORTS.includes(m.sport) ? m.sport : "volleyball";
    return;
  }
  if (m.t === "lock" && c.slot === 0) { r.locked = !!m.v; return; }
  if (m.t === "m" && m.d && typeof m.d === "object") {
    const out = JSON.stringify({ t: "m", from: c.slot, d: m.d });
    if (c.slot !== 0) { if (r.slots[0]) r.slots[0].send(out); return; }
    const lossy = m.d.k === "snap";
    r.slots.forEach((g, i) => {
      if (!g || i === 0) return;
      if (m.to !== undefined && m.to !== null && m.to !== i) return;
      if (lossy && g.backlog() > 128 * 1024) return;
      g.send(out);
    });
  }
}

// ---------- http (also serves the game page from ./public) ----------
const TYPES = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".css": "text/css", ".png": "image/png", ".ico": "image/x-icon" };
const server = http.createServer((req, res) => {
  const url = (req.url || "/").split("?")[0];
  if (url === "/healthz") { res.writeHead(200, { "Content-Type": "text/plain" }); return res.end("ok " + rooms.size + " rooms"); }
  let f = url === "/" ? "/index.html" : url;
  f = path.normalize(f).replace(/^(\.\.[\/\\])+/, "");
  const file = path.join(__dirname, "public", f);
  if (!file.startsWith(path.join(__dirname, "public"))) { res.writeHead(403); return res.end(); }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404, { "Content-Type": "text/plain" }); return res.end("Not found"); }
    res.writeHead(200, { "Content-Type": TYPES[path.extname(file)] || "application/octet-stream", "Cache-Control": "no-cache" });
    res.end(data);
  });
});
server.on("upgrade", (req, socket) => {
  const key = req.headers["sec-websocket-key"];
  if (!key || String(req.headers.upgrade).toLowerCase() !== "websocket") { socket.destroy(); return; }
  const accept = crypto.createHash("sha1").update(key + GUID).digest("base64");
  socket.write("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: " + accept + "\r\n\r\n");
  new Conn(socket, req.socket.remoteAddress);
});
// Keep connections alive through proxies and drop dead ones; remove rooms nobody is in.
const conns = () => allConns;
setInterval(() => {
  const now = Date.now();
  conns().forEach(c => { if (now - c.last > 70000) c.kill(); else c.send(Buffer.alloc(0), 0x9); });
  rooms.forEach((r, code) => { if (!r.slots[0] || !r.slots[0].alive) rooms.delete(code); });
}, 25000).unref();

if (require.main === module) server.listen(PORT, () => console.log("Room server listening on " + PORT));
module.exports = { server, rooms };
