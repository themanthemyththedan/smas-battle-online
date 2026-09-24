// Online play for the SMAS battle hack: lockstep netplay on EmulatorJS.
//
// Every player runs the whole game. Only controller input crosses the network:
// each player's buttons for frame F are sent D frames ahead of time, and nobody
// runs frame F until they hold every player's buttons for it. SNES emulation is
// deterministic, so every copy of the game stays identical. Every second each
// guest sends the host a hash of its savestate; if one ever differs, the host
// sends everyone its savestate and play continues from there (a "resync").
//
// Topology: a star. The host is player 1 and relays everything; guests talk
// only to the host. Connections are WebRTC data channels brokered by PeerJS
// (its free public server by default), so there is no game server to run.
//
// Frame stepping: EmulatorJS's core runs from requestAnimationFrame. We hold
// back those callbacks and run one only when the next frame's inputs are all
// here. A callback runs either zero frames (RetroArch's own pacing skipped it)
// or exactly one; we watch the core's frame counter to tell which.
'use strict';

import { applyBps, crc32, stripCopierHeader, targetCrc, patchedFraction, WRONG_ROM } from './bps.js';

// ---------------------------------------------------------------------------
// 1. The frame gate. Must be installed before EmulatorJS loads.

const realRAF = window.requestAnimationFrame.bind(window);
const pending = [];
let gateOn = false;
window.requestAnimationFrame = (cb) => {
  if (!gateOn) return realRAF(cb);
  pending.push(cb);
  kick();
  return 0;
};

// ---------------------------------------------------------------------------
// 2. Settings, URL parameters, small helpers.

const params = new URLSearchParams(location.search);
const ROOM_PREFIX = 'smas-battle-';
const FPS = 60.0988;                 // SNES NTSC
const HASH_EVERY = 60;               // frames between desync checks
const MAX_PLAYERS = 4;
const BUTTONS = 12;                  // RetroArch joypad ids 0..11: B Y Sel St U D L R A X L R

const $ = (id) => document.getElementById(id);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const log = (...a) => { if (params.has('debug')) console.log('[netplay]', ...a); };

function peerOptions() {
  const o = { debug: params.has('debug') ? 2 : 0 };
  if (params.get('peerhost')) {       // tests run their own PeerJS server
    o.host = params.get('peerhost');
    o.port = +(params.get('peerport') || 9000);
    o.path = params.get('peerpath') || '/';
    o.secure = params.get('peersecure') === '1';
  }
  return o;
}

function fnv(bytes) {
  let h = 0x811c9dc5;
  for (let i = 0; i < bytes.length; i++) { h ^= bytes[i]; h = Math.imul(h, 0x01000193); }
  return h >>> 0;
}

async function gzip(bytes) {
  const s = new Blob([bytes]).stream().pipeThrough(new CompressionStream('gzip'));
  return new Uint8Array(await new Response(s).arrayBuffer());
}
async function gunzip(bytes) {
  const s = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'));
  return new Uint8Array(await new Response(s).arrayBuffer());
}

function randomCode() {
  const A = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let s = '';
  for (let i = 0; i < 6; i++) s += A[Math.floor(Math.random() * A.length)];
  return s;
}

// ---------------------------------------------------------------------------
// 3. The ROM: the player's own Super Mario All-Stars, patched here.

const DB = 'smas-battle';
function idb(mode, fn) {
  return new Promise((resolve, reject) => {
    const open = indexedDB.open(DB, 1);
    open.onupgradeneeded = () => open.result.createObjectStore('files');
    open.onerror = () => reject(open.error);
    open.onsuccess = () => {
      const tx = open.result.transaction('files', mode);
      const req = fn(tx.objectStore('files'));
      tx.oncomplete = () => resolve(req && req.result);
      tx.onerror = () => reject(tx.error);
    };
  });
}
const saveSource = (bytes) => idb('readwrite', (s) => s.put(bytes, 'source')).catch(() => {});
const loadSource = () => idb('readonly', (s) => s.get('source')).catch(() => null);

let BUILD = null;          // build.json: which patch, its checksums, the EmulatorJS version
let PATCH = null;          // the .bps bytes
let ROM = null;            // the patched ROM
let ROM_CRC = 0;

async function loadBuildInfo() {
  BUILD = await (await fetch('build.json', { cache: 'no-store' })).json();
  // Keyed by the target checksum: GitHub Pages lets browsers cache files for
  // ten minutes, and an old battle.bps with a new build.json would fail.
  PATCH = new Uint8Array(await (await fetch(BUILD.patch + '?v=' + BUILD.target_crc32)).arrayBuffer());
}

// Returns what to remember for next time. Throws with a message a person can
// act on: the owner's first try was the patched Mario Battle .sfc itself.
function useSource(bytes) {
  const file = new Uint8Array(bytes);
  if (file[0] === 0x50 && file[1] === 0x4B)
    throw new Error('That is a .zip file. Unzip it first, then pick the Super Mario All-Stars (USA) .sfc inside.');
  const src = stripCopierHeader(file);   // copier-headered .smc copies work too
  if (crc32(src) === targetCrc(PATCH)) { // already exactly this build of the hack
    ROM = src;
    ROM_CRC = crc32(ROM);
    return src;
  }
  try {
    ROM = applyBps(src, PATCH);
  } catch (e) {
    if (src.length === 2097152 && patchedFraction(src, PATCH) > 0.5) {
      throw new Error('That is a Mario Battle ROM from an older build, not the original game. ' +
        'Pick the ORIGINAL Super Mario All-Stars (USA) .sfc file instead - the page patches it for you, ' +
        'so everyone in the room gets the same, newest version.');
    }
    throw new Error(e.message === 'the patch file is damaged (checksum mismatch)' ? 'The game files did not download properly. Reload the page.' : WRONG_ROM);
  }
  ROM_CRC = crc32(ROM);
  return src;
}

// ---------------------------------------------------------------------------
// 4. The emulator.

let gm = null;                // EJS_emulator.gameManager once the game is up
const localPad = new Uint8Array(BUTTONS);
const analog = new Int32Array(24);

function bootEmulator() {
  return new Promise((resolve, reject) => {
    window.EJS_player = '#game';
    window.EJS_core = 'snes';
    window.EJS_gameName = 'SMAS Battle';
    window.EJS_gameUrl = URL.createObjectURL(new Blob([ROM]));
    window.EJS_pathtodata = BUILD.ejs;
    window.EJS_startOnLoaded = true;
    window.EJS_disableLocalStorage = true;     // no saved settings / SRAM leaking in
    window.EJS_color = '#e03c28';
    window.EJS_Buttons = {                     // anything that would desync the copies
      playPause: false, restart: false, saveState: false, loadState: false,
      quickSave: false, quickLoad: false, cheat: false, cacheManager: false,
      saveSavFiles: false, loadSavFiles: false, netplay: false, exitEmulation: false,
      diskButton: false, screenRecord: false,
    };
    // RetroArch must not wait on the audio device mid-frame: in the browser
    // that wait unwinds and resumes the frame later, so a savestate taken
    // between our steps could catch a half-finished frame (CONFIRMED: with
    // audio_sync on, idle players "drifted" every few seconds; off, never).
    const EXTRA_RA = [{ name: 'audio_sync', default: 'false', isString: false }];
    let emu;
    Object.defineProperty(window, 'EJS_emulator', {
      configurable: true,
      get() { return emu; },
      set(v) {
        emu = v;
        // Port 2 gets a Super Multitap, so players 3 and 4 exist. EmulatorJS
        // 4.2.3 has no call for it and ignores input_libretro_device_p2 in
        // retroarch.cfg, but RetroArch applies it from the core's remap file
        // when the core loads (CONFIRMED: the hack's $1BFA reads 1). 257 is
        // snes9x's RETRO_DEVICE_JOYPAD_MULTITAP, (1 << 8) | JOYPAD; retro
        // port 0 is pad 1 and retro ports 1-4 are the tap's pads 2A-2D, which
        // is exactly our slots 0-3.
        v.on('saveDatabaseLoaded', (FS) => {
          const dir = '/home/web_user/retroarch/userdata/config/remaps/Snes9x';
          let path = '';
          for (const part of dir.split('/').slice(1)) {
            path += '/' + part;
            try { FS.mkdir(path); } catch (e) { /* exists */ }
          }
          FS.writeFile(dir + '/Snes9x.rmp', 'input_libretro_device_p2 = "257"\n');
        });
        let opts = [];
        Object.defineProperty(v, 'retroarchOpts', {
          configurable: true,
          get() { return opts.concat(EXTRA_RA); },
          set(x) { opts = Array.isArray(x) ? x : []; },
        });
      },
    });
    window.EJS_onGameStart = () => {
      gm = window.EJS_emulator.gameManager;
      try { gm.functions.setKeyboardEnabled(0); } catch (e) { /* older core */ }
      // Everything EmulatorJS reads from the keyboard / gamepads lands here.
      // In the lobby the game runs freely and your buttons drive player 1 of
      // your own copy; once the battle starts the lockstep loop feeds the core.
      const direct = gm.functions.simulateInput;
      gm.simulateInput = (player, index, value) => {
        if (index < BUTTONS) localPad[index] = value ? 1 : 0;
        else if (index < 24) analog[index] = value;
        if (!gateOn && index < BUTTONS) direct(0, index, value);
      };
      resolve();
    };
    const s = document.createElement('script');
    s.src = BUILD.ejs + 'loader.js';
    s.onerror = () => reject(new Error('could not load the emulator from ' + BUILD.ejs));
    document.body.appendChild(s);
  });
}

function localBits() {
  let b = 0;
  for (let i = 0; i < BUTTONS; i++) if (localPad[i]) b |= 1 << i;
  // Left stick counts as the D-pad (16 +x, 17 -x, 18 +y, 19 -y).
  const T = 0x4000;
  if (analog[16] > T) b |= 1 << 7;
  if (analog[17] > T) b |= 1 << 6;
  if (analog[18] > T) b |= 1 << 5;
  if (analog[19] > T) b |= 1 << 4;
  return b;
}

// Stop the free-running lobby game and take over frame stepping. The core
// always has exactly one frame callback scheduled; once it lands in the gate
// nothing runs behind our back. (Snapshotting a game that has only just
// powered on does not work - it never finishes booting - which is why the
// lobby lets it run first.)
async function takeControl() {
  gateOn = true;
  for (let i = 0; i < 2000 && !pending.length; i++) await sleep(1);
}

// ---------------------------------------------------------------------------
// 5. Lockstep state.

const S = {
  role: null,           // 'host' | 'guest'
  code: null,
  mySlot: -1,
  name: '',
  D: 4,                 // input delay in frames
  running: false,
  frame: 0,             // next frame to run
  localSent: 0,         // next frame we owe our own input for
  joinAt: new Map(),    // slot -> frame it joined at
  leftAt: new Map(),    // slot -> last frame it has input for
  inputs: Array.from({ length: MAX_PLAYERS }, () => new Map()),
  applied: new Int32Array(MAX_PLAYERS).fill(-1),
  hashes: new Map(),    // host: frame -> own hash;  guest: unused
  stalledSince: 0,
  lastTick: 0,
  due: 0,
  refused: 0,
  resyncs: 0,
  checks: 0,            // host: guest hashes that matched
  epoch: 0,             // bumps on every sync; hashes from an older epoch are ignored
  syncing: false,
  stopAt: Infinity,
  inHash: 0,            // running hash of every input applied, for diagnosing drift
  inHashes: new Map(),  // host: frame -> inHash
  states: new Map(),    // host, ?statediff only: frame -> savestate
};
const DIFF = params.has('statediff');

function active(slot, f) {
  const j = S.joinAt.get(slot);
  if (j === undefined || f < j) return false;
  const l = S.leftAt.get(slot);
  return !(l !== undefined && f > l);
}

function inputFor(slot, f) {
  if (!active(slot, f)) return 0;
  const v = S.inputs[slot].get(f);
  return v === undefined ? null : v;
}

function missingFor(f) {
  const m = [];
  for (let s = 0; s < MAX_PLAYERS; s++) if (inputFor(s, f) === null) m.push(s);
  return m;
}

function applyInputs(f) {
  const set = gm.functions.simulateInput;
  for (let s = 0; s < MAX_PLAYERS; s++) {
    const bits = inputFor(s, f) || 0;
    const prev = S.applied[s];
    if (bits === prev) continue;
    for (let i = 0; i < BUTTONS; i++) {
      const b = (bits >> i) & 1;
      if (prev < 0 || ((prev >> i) & 1) !== b) set(s, i, b);
    }
    S.applied[s] = bits;
  }
}

function recordInput(slot, f, bits) {
  S.inputs[slot].set(f, bits);
}

function produceLocal() {
  while (S.localSent <= S.frame + S.D) {
    const f = S.localSent++;
    if (!active(S.mySlot, f)) continue;
    const b = localBits();
    recordInput(S.mySlot, f, b);
    net.sendInput(S.mySlot, f, b);
  }
}

function prune() {
  const keep = S.frame - 600;
  if (keep <= 0 || S.frame % 300) return;
  for (const m of S.inputs) for (const k of m.keys()) if (k < keep) m.delete(k);
  for (const k of S.hashes.keys()) if (k < keep) S.hashes.delete(k);
  for (const k of S.inHashes.keys()) if (k < keep) S.inHashes.delete(k);
  for (const k of S.states.keys()) if (k < S.frame - 200) S.states.delete(k);
}

// ---------------------------------------------------------------------------
// 6. The driver: a real-rAF loop that decides when the core may run.

let kicked = false;
const mc = new MessageChannel();
mc.port1.onmessage = () => { kicked = false; tick(); };
function kick() {
  if (!S.running || kicked || S.due < 1) return;
  kicked = true;
  mc.port2.postMessage(0);
}

function loop(now) {
  if (S.running) {
    if (S.lastTick) S.due = Math.min(S.due + (now - S.lastTick) * FPS / 1000, 3);
    S.lastTick = now;
    S.refused = 0;
    tick();
    ui.status();
  }
  realRAF(loop);
}

function tick() {
  if (!S.running || S.syncing) return;
  while (S.due >= 1 && pending.length) {
    if (S.frame >= S.stopAt) return;   // tests freeze every copy on one frame
    produceLocal();
    const miss = missingFor(S.frame);
    if (miss.length) {
      if (!S.stalledSince) S.stalledSince = performance.now();
      S.waitingOn = miss;
      S.due = Math.min(S.due, 1);   // don't bank time while stalled
      return;
    }
    S.stalledSince = 0;
    S.waitingOn = null;
    applyInputs(S.frame);
    const f0 = gm.getFrameNum();
    pending.shift()(performance.now());
    const d = gm.getFrameNum() - f0;
    if (d === 0) {                  // RetroArch paced this one out; try the next
      if (++S.refused > 40) return;
      continue;
    }
    if (d !== 1) console.warn('[netplay] core ran', d, 'frames in one step');
    S.refused = 0;
    S.due -= 1;
    afterFrame(S.frame);
    S.frame += 1;
  }
}

function afterFrame(f) {
  for (let s = 0; s < MAX_PLAYERS; s++) {
    S.inHash = Math.imul(S.inHash ^ ((inputFor(s, f) || 0) + s * 4096 + f * 16384), 0x01000193) >>> 0;
  }
  if (f % HASH_EVERY === 0 && f > 0) {
    const st = gm.getState();
    const h = fnv(st);
    if (S.role === 'host') {
      S.hashes.set(f, h);
      S.inHashes.set(f, S.inHash);
      if (DIFF) S.states.set(f, st.slice());
      net.checkPendingHashes();
    } else {
      net.sendHash(f, h, S.epoch, S.inHash, DIFF ? st.slice() : null);
    }
  }
  prune();
}

// Load a savestate at frame X and carry on from there (start, resync, join).
async function applySync(msg) {
  S.syncing = true;
  try {
    const state = await gunzip(new Uint8Array(msg.st));
    await takeControl();
    gm.loadState(state);
    S.frame = msg.f;
    S.D = msg.D;
    S.joinAt = new Map(msg.join.map(([s, j]) => [s, j]));
    S.leftAt = new Map(msg.left.map(([s, l]) => [s, l]));
    for (const [s, f, b] of msg.inputs) recordInput(s, f, b);
    // Before a slot's own input starts, it holds nothing.
    for (const [s, j] of S.joinAt) if (j >= msg.f) {
      for (let f = j; f < j + S.D; f++) recordInput(s, f, 0);
    }
    const myJoin = S.joinAt.get(S.mySlot);
    if (myJoin !== undefined && myJoin >= msg.f) S.localSent = myJoin + S.D;
    S.localSent = Math.max(S.localSent, S.frame);
    S.applied.fill(-1);
    S.hashes.clear();
    S.inHashes.clear();
    S.states.clear();
    S.inHash = 0;
    S.due = 1;
    S.lastTick = 0;
    S.epoch = msg.epoch;
    S.running = true;
    if (msg.why === 'resync') S.resyncs++;
    log('sync', msg.why, 'at', msg.f, 'D', S.D, 'join', [...S.joinAt]);
  } finally {
    S.syncing = false;
  }
}

// ---------------------------------------------------------------------------
// 7. The network.

// The relay: when two players' networks will not let WebRTC connect them
// directly (strict NATs, many mobile networks), their messages go through a
// free public MQTT broker over a secure websocket instead, which works from
// anywhere. PeerJS's own TURN relays (eu-0/us-0.turn.peerjs.com) no longer
// resolve (CONFIRMED 2026-09-24), so without this such players simply could
// not join. Measured one way through these brokers: about 90-110 ms, i.e. a few
// frames more input delay - only used when the direct connection fails.
//
// Topics: smasb1/<ROOM>/h is the host's inbox; smasb1/<ROOM>/g/<id> a guest's.
// The host listens on every broker in the list; a guest uses the first one it
// reaches and the host answers on that same broker.
// Measured 2026-09-24 at 30 messages/s for 15 s: test.mosquitto.org lost 0 of
// 450 (about 90 ms, worst 100 ms), HiveMQ 0 of 450 (about 110 ms, worst 210
// ms). broker.emqx.io silently dropped two thirds, so it is not used.
// In a full relayed game test.mosquitto.org dropped the guest's connection
// mid-battle; HiveMQ held up, so it goes first.
const BROKERS = params.get('broker') ? [params.get('broker')] : ['wss://broker.hivemq.com:8884/mqtt', 'wss://test.mosquitto.org:8081/mqtt'];
const RELAY_CHUNK = 60000;
// One publish per this many ms at most, inputs and acks together: the public
// brokers start dropping well below one message per frame per client.
const RELAY_BATCH_MS = +(params.get('relaybatch') || 33);

function relayEncode(msg) {
  if (msg.st instanceof ArrayBuffer) {
    const u = new Uint8Array(msg.st);
    let s = '';
    for (let i = 0; i < u.length; i += 0x8000) s += String.fromCharCode.apply(null, u.subarray(i, i + 0x8000));
    msg = { ...msg, st: { b64: btoa(s) } };
  }
  return JSON.stringify(msg);
}
function relayDecode(text) {
  const msg = JSON.parse(text);
  if (msg.st && msg.st.b64) {
    const s = atob(msg.st.b64), u = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i);
    msg.st = u.buffer;
  }
  return msg;
}

function brokerConnect(url, timeoutMs) {
  return new Promise((resolve) => {
    let c;
    const t = setTimeout(() => { try { c.end(true); } catch (e) {} resolve(null); }, timeoutMs);
    try {
      c = mqtt.connect(url, { connectTimeout: timeoutMs, reconnectPeriod: 2000, clean: true });
    } catch (e) { clearTimeout(t); resolve(null); return; }
    c.once('connect', () => { clearTimeout(t); resolve(c); });
    for (const ev of ['close', 'offline', 'error', 'disconnect', 'reconnect']) {
      c.on(ev, (x) => log('relay', url, ev, x && (x.message || x.reasonCode || '')));
    }
  });
}

// One end of a relayed connection, shaped like a PeerJS DataConnection.
//
// The public brokers drop messages under bursts (CONFIRMED: ~10 of 60 lost
// each way when a battle starts, QoS 0, no error), and lockstep cannot lose a
// single input. So this is a tiny reliable, ordered channel on top: every item
// carries a sequence number, the receiver acknowledges the highest one it has
// in order, and the sender resends anything unacknowledged after 400 ms.
// Items queued within a few milliseconds share one publish, which also keeps
// the message rate down.
class RelayConn {
  constructor(client, outTopic, from) {
    this.client = client; this.outTopic = outTopic; this.from = from;
    this.open = true; this.relay = true; this.handlers = {}; this.parts = new Map();
    this.lastSeen = performance.now();
    this.sent = 0; this.recv = 0;
    this.nextSeq = 0; this.unacked = new Map();   // seq -> { item, t }
    this.expect = 0; this.early = new Map();      // seq -> item (arrived out of order)
    this.queue = []; this.flushTimer = 0; this.needAck = false;
    this.srtt = 500;                              // smoothed ack round trip, ms
    this.resent = 0;
    this.retry = setInterval(() => this.resend(), 200);
  }
  on(ev, fn) { (this.handlers[ev] = this.handlers[ev] || []).push(fn); }
  emit(ev, x) { for (const fn of this.handlers[ev] || []) fn(x); }
  send(msg) {
    if (!this.open) return;
    this.sent++;
    const text = relayEncode(msg);
    if (text.length <= RELAY_CHUNK) this.queue.push(text);
    else {
      const id = Math.random().toString(36).slice(2), n = Math.ceil(text.length / RELAY_CHUNK);
      for (let i = 0; i < n; i++) this.queue.push({ id, i, n, d: text.slice(i * RELAY_CHUNK, (i + 1) * RELAY_CHUNK) });
    }
    this.schedule();
  }
  schedule() {
    if (!this.flushTimer) this.flushTimer = setTimeout(() => { this.flushTimer = 0; this.flush(); }, RELAY_BATCH_MS);
  }
  publish(items) {
    const env = { ack: this.expect - 1, m: items };
    if (this.from) env.from = this.from;
    this.needAck = false;
    this.client.publish(this.outTopic, JSON.stringify(env));
  }
  flush() {
    if (!this.open) return;
    const now = performance.now();
    let batch = [], size = 0;
    for (const item of this.queue) {
      const seq = this.nextSeq++;
      this.unacked.set(seq, { item, t: now, first: now, tries: 0 });
      const len = typeof item === 'string' ? item.length : item.d.length;
      if (batch.length && size + len > RELAY_CHUNK) { this.publish(batch); batch = []; size = 0; }
      batch.push([seq, item]); size += len;
    }
    this.queue = [];
    if (batch.length || this.needAck) this.publish(batch);
  }
  resend() {
    if (!this.open) return;
    const now = performance.now();
    let batch = [], size = 0;
    for (const [seq, u] of this.unacked) {
      // Resend only what is clearly lost: the relay's round trip is 250-400
      // ms, and resending on a fixed 300 ms timer doubled the traffic and got
      // us throttled.
      if (now - u.t < Math.max(400, 2 * this.srtt)) continue;
      u.t = now; u.tries++; this.resent++;
      const len = typeof u.item === 'string' ? u.item.length : u.item.d.length;
      if (batch.length && size + len > RELAY_CHUNK) { this.publish(batch); batch = []; size = 0; }
      batch.push([seq, u.item]); size += len;
    }
    if (batch.length || this.needAck) this.publish(batch);
  }
  receive(env) {                       // env: a parsed envelope from the broker
    this.lastSeen = performance.now();
    if (env.bye) { this.close(false); return; }
    if (typeof env.ack === 'number') {
      const now = performance.now();
      for (const [seq, u] of this.unacked) {
        if (seq > env.ack) continue;
        if (!u.tries) this.srtt = 0.8 * this.srtt + 0.2 * (now - u.first);
        this.unacked.delete(seq);
      }
    }
    if (!env.m || !env.m.length) return;
    for (const [seq, item] of env.m) if (seq >= this.expect) this.early.set(seq, item);
    this.needAck = true;
    this.schedule();
    while (this.early.has(this.expect)) {
      const item = this.early.get(this.expect);
      this.early.delete(this.expect);
      this.expect++;
      this.deliver(item);
    }
  }
  deliver(item) {
    let text = item;
    if (typeof item !== 'string') {
      const p = this.parts.get(item.id) || [];
      p[item.i] = item.d;
      this.parts.set(item.id, p);
      if (p.filter((x) => x !== undefined).length < item.n) return;
      this.parts.delete(item.id);
      text = p.join('');
    }
    this.recv++;
    this.emit('data', relayDecode(text));
  }
  close(tell = true) {
    if (!this.open) return;
    this.open = false;
    clearInterval(this.retry);
    if (tell) try { this.client.publish(this.outTopic, JSON.stringify({ from: this.from, bye: 1 })); } catch (e) {}
    this.emit('close');
  }
}

const net = {
  peer: null,
  conns: new Map(),        // host: slot -> DataConnection;  guest: 0 -> host
  names: new Map(),        // slot -> name
  ready: new Set(),        // host: slots whose emulator is booted
  rtt: new Map(),          // host: slot -> ms
  guestHashes: new Map(),  // host: `${slot}:${frame}` -> hash

  send(conn, msg) { try { if (conn && conn.open) conn.send(msg); } catch (e) { log('send failed', e); } },
  broadcast(msg, except = -1) { for (const [s, c] of this.conns) if (s !== except) this.send(c, msg); },

  sendInput(slot, f, b) {
    const m = { t: 'i', s: slot, f, b };
    if (S.role === 'host') this.broadcast(m); else this.send(this.conns.get(0), m);
  },
  sendHash(f, h, e, ih, st) { this.send(this.conns.get(0), { t: 'h', f, h, e, ih, st: st && st.buffer }); },

  // -- host --------------------------------------------------------------
  host() {
    return new Promise((resolve, reject) => {
      S.role = 'host';
      S.mySlot = 0;
      S.code = params.get('room') || randomCode();
      this.names.set(0, S.name);
      this.peer = new Peer(ROOM_PREFIX + S.code, peerOptions());
      this.peer.on('open', () => resolve());
      this.peer.on('error', (e) => {
        if (e.type === 'unavailable-id') { ui.error('That room code is taken. Reload the page to get a new one.'); reject(e); return; }
        if (e.type === 'peer-unavailable') return;          // a guest vanished mid-handshake
        ui.error('Connection problem: ' + (e.type || e.message) + '. Friends can still join through the relay.');
        resolve();                                          // the relay still works
      });
      // The broker drops idle registrations (sleeping laptop, flaky Wi-Fi);
      // re-register so the room link keeps working.
      this.peer.on('disconnected', () => setTimeout(() => { try { this.peer.reconnect(); } catch (e) {} }, 1000));
      this.peer.on('connection', (c) => this.onGuest(c));
      if (!params.has('norelay')) this.hostRelay();
      setInterval(() => this.ping(), 1000);
    });
  },

  // Listen for relayed guests on every broker (see RelayConn).
  hostRelay() {
    const inbox = 'smasb1/' + S.code + '/h';
    const guests = new Map();                 // guest id -> RelayConn
    for (const url of BROKERS) {
      brokerConnect(url, 8000).then((client) => {
        if (!client) { log('relay broker unreachable', url); return; }
        client.subscribe(inbox);
        client.on('message', (topic, payload) => {
          let env;
          try { env = JSON.parse(payload.toString()); } catch (e) { return; }
          if (!env.from) return;
          let conn = guests.get(env.from);
          if (!conn) {
            if (env.bye) return;
            conn = new RelayConn(client, 'smasb1/' + S.code + '/g/' + env.from);
            guests.set(env.from, conn);
            conn.on('close', () => guests.delete(env.from));
            log('relay guest', env.from, 'via', url);
            this.onGuest(conn);
            conn.emit('open');
          }
          conn.receive(env);
        });
      });
    }
    // A relayed guest answers a ping every second; silence means it is gone.
    setInterval(() => {
      for (const c of guests.values()) if (performance.now() - c.lastSeen > 30000) c.close();
    }, 2000);
  },

  freeSlot() {
    for (let s = 1; s < MAX_PLAYERS; s++) if (!this.conns.has(s)) return s;
    return -1;
  },

  onGuest(conn) {
    conn.on('open', () => {
      const slot = this.freeSlot();
      if (slot < 0) { this.send(conn, { t: 'full' }); setTimeout(() => conn.close(), 500); return; }
      conn.slot = slot;
      conn.on('data', (m) => this.fromGuest(conn, m));
      conn.on('close', () => this.guestLeft(conn));
      conn.on('error', () => this.guestLeft(conn));
    });
  },

  fromGuest(conn, m) {
    const slot = conn.slot;
    switch (m.t) {
      case 'hello':
        if (m.crc !== ROM_CRC) {
          this.send(conn, { t: 'reject', why: 'Your patched ROM does not match the host\'s. Make sure you both opened the same link, then reload.' });
          setTimeout(() => conn.close(), 500);
          return;
        }
        this.conns.set(slot, conn);
        this.names.set(slot, String(m.name || ('Player ' + (slot + 1))).slice(0, 16));
        this.send(conn, { t: 'welcome', slot, running: S.running });
        this.lobby();
        break;
      case 'ready':
        this.ready.add(slot);
        if (S.running) this.sync('join', [slot]);
        this.lobby();
        break;
      case 'i':
        if (m.s !== slot) return;
        recordInput(slot, m.f, m.b);
        this.broadcast(m, slot);
        kick();
        break;
      case 'h':
        if (m.e !== S.epoch) return;          // computed before the last sync
        this.guestHashes.set(slot + ':' + m.f, m);
        this.checkPendingHashes();
        break;
      case 'pong': {
        // Median of the last five: one slow ping must not set the delay.
        const h = (conn.rtts = (conn.rtts || []).concat(performance.now() - m.at).slice(-5));
        this.rtt.set(slot, [...h].sort((x, y) => x - y)[h.length >> 1]);
        break;
      }
    }
  },

  guestLeft(conn) {
    const slot = conn.slot;
    if (slot === undefined || this.conns.get(slot) !== conn) return;
    this.conns.delete(slot);
    this.ready.delete(slot);
    this.rtt.delete(slot);
    ui.toast((this.names.get(slot) || 'A player') + ' left');
    this.names.delete(slot);
    if (S.joinAt.has(slot) && !S.leftAt.has(slot)) {
      let last = S.joinAt.get(slot) + S.D - 1;
      for (const f of S.inputs[slot].keys()) if (f > last) last = f;
      S.leftAt.set(slot, last);
      this.broadcast({ t: 'left', s: slot, f: last });
      kick();
    }
    this.lobby();
  },

  ping() {
    this.broadcast({ t: 'ping', at: performance.now() });
    if (!S.running) this.lobby();
  },

  lobby() {
    const players = [];
    for (let s = 0; s < MAX_PLAYERS; s++) if (this.names.has(s)) {
      players.push({ s, name: this.names.get(s), ready: s === 0 ? !!gm : this.ready.has(s), rtt: Math.round(this.rtt.get(s) || 0) });
    }
    this.lobbyState = { players, running: S.running, D: S.D };
    this.broadcast({ t: 'lobby', ...this.lobbyState });
    ui.lobby(this.lobbyState);
  },

  pickDelay() {
    if (params.get('delay')) return Math.max(1, Math.min(20, +params.get('delay')));
    // Worst one-way path is guest -> host -> guest: half of each of the two
    // worst round trips, plus slack. A relayed guest counts its whole round
    // trip: the public brokers' delay swings, and too tight a delay halves the
    // frame rate (CONFIRMED: 12 frames over HiveMQ ran at ~30 fps).
    let relayed = false;
    const eff = [...this.rtt.entries()].map(([s, r]) => {
      const c = this.conns.get(s);
      if (c && c.relay) { relayed = true; return r; }
      return r / 2;
    }).sort((a, b) => b - a);
    const path = (eff[0] || 0) + (eff[1] || 0);
    return Math.max(2, Math.min(relayed ? 30 : 12, Math.ceil(path / (1000 / FPS)) + 2));
  },

  // Snapshot the host at its current frame and bring everyone onto it.
  async sync(why, newSlots = []) {
    if (S.syncing) { setTimeout(() => this.sync(why, newSlots), 200); return; }
    S.syncing = true;
    let msg;
    try {
      await takeControl();
      if (why === 'start') {
        S.frame = 0;
        S.D = this.pickDelay();
        S.joinAt = new Map([[0, 0]]);
        S.leftAt = new Map();
        for (const s of this.ready) if (this.conns.has(s)) S.joinAt.set(s, 0);
      }
      const X = S.frame;
      for (const s of newSlots) { S.joinAt.set(s, X); S.leftAt.delete(s); }
      const state = gm.getState();
      const inputs = [];
      for (let s = 0; s < MAX_PLAYERS; s++) for (const [f, b] of S.inputs[s]) if (f >= X) inputs.push([s, f, b]);
      msg = {
        t: 'sync', why, f: X, D: S.D, epoch: S.epoch + 1,
        st: (await gzip(state)).buffer,
        join: [...S.joinAt], left: [...S.leftAt], inputs,
      };
      this.guestHashes.clear();
    } finally {
      S.syncing = false;
    }
    for (const [s, c] of this.conns) if (S.joinAt.has(s)) this.send(c, msg);
    await applySync(msg);
    this.lobby();
  },

  checkPendingHashes() {
    for (const [key, m] of this.guestHashes) {
      const [slot, f] = key.split(':').map(Number);
      const mine = S.hashes.get(f);
      if (mine === undefined) { if (f < S.frame - 600) this.guestHashes.delete(key); continue; }
      this.guestHashes.delete(key);
      if (mine === m.h) { S.checks++; continue; }
      const sameInput = S.inHashes.get(f) === m.ih;
      console.warn('[netplay] player', slot + 1, 'drifted at frame', f, sameInput ? '(same inputs)' : '(DIFFERENT inputs)', '- resyncing');
      if (DIFF && m.st && S.states.has(f)) {
        const a = S.states.get(f), b = new Uint8Array(m.st), out = [];
        for (let i = 0, q = -1; i <= a.length; i++) {
          const d = i < a.length && a[i] !== b[i];
          if (d && q < 0) q = i;
          if (!d && q >= 0) { out.push(q + '+' + (i - q) + ' ' + [...a.slice(q, Math.min(i, q + 6))].join('.') + '/' + [...b.slice(q, Math.min(i, q + 6))].join('.')); q = -1; }
        }
        console.warn('[netplay] diff', out.length, 'ranges:', out.slice(0, 40).join('  '));
      }
      this.sync('resync');
      return;
    }
  },

  // -- guest -------------------------------------------------------------
  join(code) {
    return new Promise((resolve, reject) => {
      S.role = 'guest';
      S.code = code;
      let done = false;
      const welcome = () => { if (!done) { done = true; clearTimeout(giveUp); resolve(); } };
      const fail = (why) => { if (!done) { done = true; clearTimeout(giveUp); ui.error(why); reject(new Error(why)); } };
      // First conversation to open wins; a later one is closed.
      const use = (c) => {
        if (done || this.conns.has(0)) { try { c.close(); } catch (e) {} return; }
        this.conns.set(0, c);
        c.on('data', (m) => this.fromHost(m, welcome, fail));
        c.on('close', () => {
          if (this.conns.get(0) !== c) return;
          S.running = false;
          if (done) ui.error('The host left the game.');
        });
        this.send(c, { t: 'hello', name: S.name, crc: ROM_CRC });
      };
      const NO_ROOM = 'Could not reach that room. Check the host still has the page open (not closed or asleep), or ask them for a new link.';
      let giveUp = setTimeout(() => fail(NO_ROOM), 30000);

      // 1. Direct (WebRTC via PeerJS).
      let relayStarted = false;
      const relay = () => {
        if (relayStarted || done || this.conns.has(0) || params.has('norelay')) return;
        relayStarted = true;
        ui.note('Direct connection is blocked by one of your networks - connecting through the relay…');
        this.guestRelay(code, use);
      };
      if (!params.has('relay')) {
        this.peer = new Peer(undefined, peerOptions());
        this.peer.on('error', (e) => {
          log('peer error', e.type);
          // The broker says nobody holds that room: give the relay a short
          // chance (the host may be relay-only) rather than the full wait.
          if (e.type === 'peer-unavailable') { clearTimeout(giveUp); giveUp = setTimeout(() => fail(NO_ROOM), 12000); }
          relay();
        });
        this.peer.on('open', () => {
          const c = this.peer.connect(ROOM_PREFIX + code, { reliable: true });
          c.on('open', () => use(c));
        });
        setTimeout(relay, 7000);                // no direct connection yet: 2. the relay
      } else {
        relay();                                // ?relay forces it (tests)
      }
    });
  },

  async guestRelay(code, use) {
    const id = Math.random().toString(36).slice(2, 12);
    for (const url of BROKERS) {
      const client = await brokerConnect(url, 8000);
      if (!client) { log('relay broker unreachable', url); continue; }
      const conn = new RelayConn(client, 'smasb1/' + code + '/h', id);
      client.subscribe('smasb1/' + code + '/g/' + id, () => {
        client.on('message', (t, payload) => {
          try { conn.receive(JSON.parse(payload.toString())); } catch (e) { log('bad relay message', e); }
        });
        use(conn);
      });
      // The host pings every second; silence means it is gone.
      setInterval(() => { if (conn.open && performance.now() - conn.lastSeen > 30000) conn.close(); }, 2000);
      window.addEventListener('pagehide', () => conn.close());
      return;
    }
    ui.error('Could not reach the relay either. Check your internet connection and try again.');
  },

  fromHost(m, onWelcome, onFail) {
    switch (m.t) {
      case 'welcome': S.mySlot = m.slot; ui.note(''); onWelcome(); break;
      case 'full': onFail('That room already has four players.'); break;
      case 'reject': onFail(m.why); break;
      case 'lobby': this.lobbyState = m; ui.lobby(m); break;
      case 'ping': this.send(this.conns.get(0), { t: 'pong', at: m.at }); break;
      case 'i': recordInput(m.s, m.f, m.b); kick(); break;
      case 'left': S.leftAt.set(m.s, m.f); kick(); break;
      case 'sync': applySync(m).then(() => ui.playing()); break;
    }
  },
};

// ---------------------------------------------------------------------------
// 8. The page.

const ui = {
  show(id) {
    for (const el of document.querySelectorAll('.panel')) el.hidden = el.id !== id;
  },
  note(msg) {
    $('romstate').textContent = msg || $('romstate').textContent;
    if (msg) $('romstate').classList.add('busy'); else $('romstate').classList.remove('busy');
  },
  error(msg) {
    $('error').textContent = msg;
    $('error').hidden = false;
  },
  toast(msg) {
    const t = $('toast');
    t.textContent = msg;
    t.hidden = false;
    clearTimeout(this._t);
    this._t = setTimeout(() => { t.hidden = true; }, 3000);
  },
  link() {
    const u = new URL(location.href);
    u.hash = S.code;
    return u.toString();
  },
  lobby(st) {
    const list = $('players');
    list.textContent = '';
    for (let s = 0; s < MAX_PLAYERS; s++) {
      const p = st.players.find((x) => x.s === s);
      const li = document.createElement('li');
      li.className = 'p' + (s + 1) + (p ? '' : ' empty');
      const tag = document.createElement('b');
      tag.textContent = 'P' + (s + 1);
      li.appendChild(tag);
      const nm = document.createElement('span');
      nm.textContent = p ? p.name + (s === S.mySlot ? ' (you)' : '') : 'open';
      li.appendChild(nm);
      const meta = document.createElement('i');
      if (p) meta.textContent = (p.ready ? 'ready' : 'loading…') + (s > 0 && p.rtt ? ' · ' + p.rtt + ' ms' : '');
      li.appendChild(meta);
      list.appendChild(li);
    }
    const others = st.players.filter((p) => p.s !== 0);
    const allReady = st.players.every((p) => p.ready);
    if (S.role === 'host') {
      $('start').hidden = st.running;
      $('start').disabled = !gm || !allReady || others.length === 0;
      $('start').textContent = others.length === 0 ? 'Waiting for friends…' : allReady ? 'Start (' + st.players.length + ' players)' : 'Waiting for everyone to load…';
    } else {
      $('start').hidden = true;
    }
    $('waitmsg').hidden = S.role === 'host' || st.running;
  },
  playing() {
    document.body.classList.add('playing');
  },
  status() {
    const el = $('status');
    const parts = ['P' + (S.mySlot + 1), 'delay ' + S.D + 'f'];
    if (S.resyncs) parts.push(S.resyncs + ' resync' + (S.resyncs > 1 ? 's' : ''));
    el.textContent = parts.join(' · ');
    const w = $('waiting');
    if (S.stalledSince && performance.now() - S.stalledSince > 400 && S.waitingOn) {
      const who = S.waitingOn.map((s) => net.names.get(s) || (net.lobbyState?.players.find((p) => p.s === s)?.name) || 'P' + (s + 1));
      w.textContent = 'Waiting for ' + who.join(', ') + '…';
      w.hidden = false;
    } else {
      w.hidden = true;
    }
  },
};

async function start() {
  S.name = (localStorage.getItem('smas-name') || '').slice(0, 16);
  $('name').value = S.name;
  $('name').addEventListener('change', () => {
    S.name = $('name').value.trim().slice(0, 16);
    try { localStorage.setItem('smas-name', S.name); } catch (e) {}
  });

  const code = location.hash.replace('#', '').toUpperCase();
  $('go').textContent = code ? 'Join room ' + code : 'Create a room';
  $('intro-join').hidden = !code;
  $('intro-host').hidden = !!code;
  // An old room link in the address bar makes this a guest page; one click
  // gets back to hosting (the owner got stuck on "Join room" this way).
  $('own').hidden = !code;
  $('own').addEventListener('click', () => {
    location.href = location.pathname + location.search;   // same page, no room code
  });
  window.addEventListener('hashchange', () => location.reload());

  // Listen for a picked ROM straight away; the patch may still be downloading.
  const buildReady = loadBuildInfo();
  // The file box: click to choose, or drop the file on it (or anywhere).
  const drop = $('drop');
  const showRom = (ok, text) => {
    drop.classList.toggle('ok', ok);
    drop.classList.toggle('bad', !ok);
    $('dropmain').textContent = ok ? 'Game file ready ✓' : 'That file will not work - drop or choose another';
    $('romstate').textContent = text;
  };
  const refresh = () => { $('go').classList.toggle('waiting', !ROM); };
  const takeFile = async (f) => {
    if (!f) return;
    $('error').hidden = true;
    try {
      const bytes = await f.arrayBuffer();
      await buildReady;
      const src = useSource(bytes);
      await saveSource(src);
      showRom(true, f.name + ' - checked and ready. You can create a room.');
    } catch (e) {
      ROM = null;
      showRom(false, e.message);
    }
    refresh();
  };
  $('romfile').addEventListener('change', () => takeFile($('romfile').files[0]));
  for (const ev of ['dragenter', 'dragover']) window.addEventListener(ev, (e) => { e.preventDefault(); drop.classList.add('over'); });
  for (const ev of ['dragleave', 'drop']) window.addEventListener(ev, (e) => { e.preventDefault(); drop.classList.remove('over'); });
  window.addEventListener('drop', (e) => takeFile(e.dataTransfer && e.dataTransfer.files[0]));

  try {
    await buildReady;
  } catch (e) {
    ui.error('Could not load the game files (build.json / patch).');
    return;
  }
  $('version').textContent = 'build ' + BUILD.commit;

  const cached = await loadSource();
  if (cached && !ROM) {
    try { useSource(cached); showRom(true, 'Using the game file you picked last time. Drop another one here to change it.'); }
    catch (e) { ROM = null; }
  }
  refresh();

  $('go').addEventListener('click', async () => {
    if (!ROM) {                       // nothing picked yet: say so and open the chooser
      showRom(false, 'First choose your Super Mario All-Stars (USA) .sfc file - it is the game file itself.');
      $('dropmain').textContent = 'Choose your game file first';
      $('romfile').click();
      return;
    }
    $('go').disabled = true;
    $('error').hidden = true;
    S.name = $('name').value.trim().slice(0, 16) || (code ? 'Guest' : 'Host');
    try {
      if (code) {
        await net.join(code);
      } else {
        await net.host();
        history.replaceState(null, '', ui.link());
      }
    } catch (e) {
      $('go').disabled = false;
      return;
    }
    ui.show('lobby');
    $('link').value = ui.link();
    $('linkrow').hidden = S.role !== 'host';
    await bootEmulator();
    if (S.role === 'host') net.lobby();
    else net.send(net.conns.get(0), { t: 'ready' });
  });

  $('copy').addEventListener('click', async () => {
    try { await navigator.clipboard.writeText($('link').value); ui.toast('Link copied'); }
    catch (e) { $('link').select(); }
  });
  $('start').addEventListener('click', async () => {
    $('start').disabled = true;
    await net.sync('start');
    ui.playing();
  });

  realRAF(loop);
}

// Exposed for the automated two-browser test (scripts/verify_netplay.js).
window.__netplay = { S, net, get gm() { return gm; }, localPad, fnv };

start();
