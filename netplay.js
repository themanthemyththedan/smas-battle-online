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

import { applyBps, crc32 } from './bps.js?v=31ad4b0';

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

// Relay (TURN) servers for players whose networks block a direct link: the
// owner's free Metered account (app smas-battle, 500 MB/month, no billing;
// set up 2026-09-25). This key is meant to sit in a public page - it only
// hands out short-lived relay logins. If it fails we fall back to public
// STUN, and past that to the MQTT relay (RelayConn).
const TURN_API = 'https://smas-battle.metered.live/api/v1/turn/credentials?apiKey=20ae283f94f3574a20ee1f93b33c2938f838';
let ICE = [{ urls: 'stun:stun.l.google.com:19302' }];
async function loadIce() {
  try {
    const ctl = new AbortController();
    const t = setTimeout(() => ctl.abort(), 5000);
    const list = await (await fetch(TURN_API, { signal: ctl.signal })).json();
    clearTimeout(t);
    if (Array.isArray(list) && list.length) ICE = [{ urls: 'stun:stun.l.google.com:19302' }, ...list];
  } catch (e) { log('TURN servers unavailable', e); }
}

function peerOptions() {
  const o = { debug: params.has('debug') ? 2 : 0, config: { iceServers: ICE } };
  // ?turnonly: force every connection through the relay (tests the path a
  // friend behind a strict network would take).
  if (params.has('turnonly')) o.config.iceTransportPolicy = 'relay';
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

function loadPrefs() {
  try { return JSON.parse(localStorage.getItem('smas-prefs') || '{}') || {}; } catch (e) { return {}; }
}
function savePrefs(p) {
  try { localStorage.setItem('smas-prefs', JSON.stringify({ ...loadPrefs(), ...p })); } catch (e) {}
}

// A per-room identity, so a player who drops can get their own slot back.
function roomToken(code) {
  const k = 'smas-token-' + code;
  let t = null;
  try { t = localStorage.getItem(k); } catch (e) {}
  if (!t) {
    t = Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
    try { localStorage.setItem(k, t); } catch (e) {}
  }
  return t;
}

function randomCode() {
  const A = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let s = '';
  for (let i = 0; i < 6; i++) s += A[Math.floor(Math.random() * A.length)];
  return s;
}

// ---------------------------------------------------------------------------
// 3. The ROM: the owner's own cartridge dump, locked with a password.
//
// game.bin is the original Super Mario All-Stars, gzipped and encrypted with
// AES-256-GCM under PBKDF2-SHA256(password) (scripts/lock_rom.py has the
// layout). Nobody picks a file: the password opens game.bin, and battle.bps
// turns it into the hack, here in the browser. A wrong password fails GCM's
// tag check. The derived key (not the password) is remembered per browser,
// tied to game.bin's salt, so a new password shuts out old browsers too.

let BUILD = null;          // build.json: which patch, its checksums, the EmulatorJS version
let PATCH = null;          // the .bps bytes
let LOCKED = null;         // game.bin
let ROM = null;            // the patched ROM
let ROM_CRC = 0;
const KEY_ITEM = 'smas-key';

async function loadBuildInfo() {
  BUILD = await (await fetch('build.json', { cache: 'no-store' })).json();
  // Keyed by the target checksum: GitHub Pages lets browsers cache files for
  // ten minutes, and an old battle.bps with a new build.json would fail.
  const [patch, locked] = await Promise.all([
    fetch(BUILD.patch + '?v=' + BUILD.target_crc32).then((r) => r.arrayBuffer()),
    fetch('game.bin', { cache: 'no-store' }).then((r) => { if (!r.ok) throw new Error('game.bin ' + r.status); return r.arrayBuffer(); }),
  ]);
  PATCH = new Uint8Array(patch);
  LOCKED = new Uint8Array(locked);
}

const lockParts = () => {
  const b = LOCKED, v = new DataView(b.buffer, b.byteOffset);
  if (String.fromCharCode(...b.subarray(0, 8)) !== 'SMASLOCK' || b[8] !== 1) throw new Error('game.bin is not a locked ROM');
  return { iters: v.getUint32(9, true), salt: b.subarray(13, 29), iv: b.subarray(29, 41), body: b.subarray(41) };
};
const hex = (b) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');

async function deriveKey(password) {
  const { iters, salt } = lockParts();
  const base = await crypto.subtle.importKey('raw', new TextEncoder().encode(password), 'PBKDF2', false, ['deriveBits']);
  return new Uint8Array(await crypto.subtle.deriveBits({ name: 'PBKDF2', hash: 'SHA-256', salt, iterations: iters }, base, 256));
}

// Opens game.bin with a raw 32-byte key and patches it. Throws 'wrong' if the
// key does not fit (wrong password, or game.bin was re-locked since).
async function openRom(raw) {
  const { iv, body } = lockParts();
  const key = await crypto.subtle.importKey('raw', raw, 'AES-GCM', false, ['decrypt']);
  let src;
  try { src = new Uint8Array(await crypto.subtle.decrypt({ name: 'AES-GCM', iv }, key, body)); }
  catch (e) { throw new Error('wrong'); }
  src = await gunzip(src);
  try { ROM = applyBps(src, PATCH); }
  catch (e) { throw new Error('The game files did not download properly. Reload the page.'); }
  ROM_CRC = crc32(ROM);
}

function rememberKey(raw) {
  try { localStorage.setItem(KEY_ITEM, JSON.stringify({ salt: hex(lockParts().salt), key: hex(raw) })); } catch (e) {}
}
function rememberedKey() {
  try {
    const k = JSON.parse(localStorage.getItem(KEY_ITEM) || 'null');
    if (k && k.salt === hex(lockParts().salt)) return new Uint8Array(k.key.match(/../g).map((h) => parseInt(h, 16)));
  } catch (e) {}
  return null;
}
function forgetKey() { try { localStorage.removeItem(KEY_ITEM); } catch (e) {} }

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
      settings: false,                          // core options: one player changing them would desync
    };
    // Phones: the stock SNES touch layout minus Fast/Slow, which netplay ignores.
    window.EJS_VirtualGamepadSettings = [
      { type: 'button', text: 'X', id: 'x', location: 'right', left: 40, bold: true, input_value: 9 },
      { type: 'button', text: 'Y', id: 'y', location: 'right', top: 40, bold: true, input_value: 1 },
      { type: 'button', text: 'A', id: 'a', location: 'right', left: 81, top: 40, bold: true, input_value: 8 },
      { type: 'button', text: 'B', id: 'b', location: 'right', left: 40, top: 80, bold: true, input_value: 0 },
      { type: 'dpad', id: 'dpad', location: 'left', left: '50%', top: '50%', joystickInput: false, inputValues: [4, 5, 6, 7] },
      { type: 'button', text: 'Start', id: 'start', location: 'center', left: 60, fontSize: 15, block: true, input_value: 3 },
      { type: 'button', text: 'Select', id: 'select', location: 'center', left: -5, fontSize: 15, block: true, input_value: 2 },
      // L and R below the pads (stock: above them, over the picture).
      { type: 'button', text: 'L', id: 'l', location: 'left', left: 3, top: 140, bold: true, block: true, input_value: 10 },
      { type: 'button', text: 'R', id: 'r', location: 'right', right: 3, top: 140, bold: true, block: true, input_value: 11 },
    ];
    // Controls and volume live in our own storage (EmulatorJS's is off, since
    // it would also keep core options): restore them, and save on change.
    const saved = loadPrefs();
    if (saved.controls) window.EJS_defaultControls = saved.controls;
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
        v.saveSettings = function () {
          savePrefs({ controls: this.controls, volume: this.volume, muted: this.muted });
        };
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
      const pv = loadPrefs();
      if (typeof pv.volume === 'number') {
        try { window.EJS_emulator.volume = pv.volume; window.EJS_emulator.setVolume(pv.muted ? 0 : pv.volume); } catch (e) {}
      }
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
  pausedBy: null,       // name of whoever paused, while everyone is paused
  away: new Set(),      // slots whose tab is hidden (their game cannot run)
  locked: false,        // host: refuse new players (rejoins still allowed)
  delayChoice: 'auto',  // host: 'auto' or a fixed input delay in frames
  kicked: false,
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

// Pause: every copy stops on frame m.f (see net.pause); resume lifts it.
function applyPause(m) {
  S.pausedBy = m.by || 'someone';
  S.stopAt = m.f;
  ui.paused();
}
function applyResume() {
  S.pausedBy = null;
  S.stopAt = Infinity;
  ui.paused();
  kick();
}

// Load a savestate at frame X and carry on from there (start, resync, join).
async function applySync(msg) {
  if (!gm) return;                     // our emulator is not up yet; the host syncs us on 'ready'
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
    if (msg.why === 'delay') ui.toast('Input delay is now ' + S.D + ' frames');
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
  reserved: new Map(),     // host: token -> { slot, name, until } for dropped players
  banned: new Set(),       // host: tokens of kicked players
  REJOIN_MS: 180000,

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

  // A slot is free if nobody holds it and no dropped player is due back.
  freeSlot() {
    const now = performance.now(), held = new Set();
    for (const [t, r] of this.reserved) { if (r.until < now) this.reserved.delete(t); else held.add(r.slot); }
    for (let s = 1; s < MAX_PLAYERS; s++) if (!this.conns.has(s) && !held.has(s)) return s;
    return -1;
  },

  onGuest(conn) {
    conn.on('open', () => {
      conn.on('data', (m) => this.fromGuest(conn, m));
      conn.on('close', () => this.guestLeft(conn));
      conn.on('error', () => this.guestLeft(conn));
    });
  },

  refuse(conn, t, why) {
    this.send(conn, { t, why });
    setTimeout(() => { try { conn.close(); } catch (e) {} }, 500);
  },

  hello(conn, m) {
    if (conn.slot !== undefined) return;
    if (m.crc !== ROM_CRC) {
      this.refuse(conn, 'reject', "Your game file is a different version from the host's. Both of you: reload the page, then pick the ORIGINAL Super Mario All-Stars (USA) file.");
      return;
    }
    if (m.token && this.banned.has(m.token)) { this.refuse(conn, 'reject', 'The host removed you from this room.'); return; }
    let slot = -1, back = false;
    const r = m.token && this.reserved.get(m.token);
    if (r && r.until > performance.now() && !this.conns.has(r.slot)) {
      slot = r.slot; back = true;                         // rejoining after a drop
      this.reserved.delete(m.token);
    } else if (m.token) {
      for (const [s, c] of this.conns) {                  // same player, new tab / reload
        if (c.token === m.token) { slot = s; back = true; c.replaced = true; this.conns.delete(s); try { c.close(); } catch (e) {} }
      }
    }
    if (slot < 0) {
      if (S.locked) { this.refuse(conn, 'reject', 'The host has locked this room. Ask them to unlock it.'); return; }
      slot = this.freeSlot();
      if (slot < 0) { this.refuse(conn, 'full'); return; }
    }
    conn.slot = slot;
    conn.token = m.token;
    this.conns.set(slot, conn);
    this.ready.delete(slot);
    S.away.delete(slot);
    this.names.set(slot, String(m.name || ('Player ' + (slot + 1))).slice(0, 16));
    this.send(conn, { t: 'welcome', slot, running: S.running });
    if (back) ui.toast(this.names.get(slot) + ' is back');
    this.lobby();
  },

  fromGuest(conn, m) {
    if (m.t === 'hello') { this.hello(conn, m); return; }
    const slot = conn.slot;
    if (slot === undefined || this.conns.get(slot) !== conn) return;
    switch (m.t) {
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
      case 'away':
        if (m.on) S.away.add(slot); else S.away.delete(slot);
        this.lobby();
        break;
      case 'pause': this.pause(this.names.get(slot)); break;
      case 'resume': this.resume(); break;
    }
  },

  // Everyone stops on the same frame: the host's frame plus the input delay
  // plus one - no copy can have got further than that (it would need the
  // host's buttons for it, which do not exist yet).
  pause(by) {
    if (!S.running || S.pausedBy) return;
    const m = { t: 'pause', f: S.frame + S.D + 1, by: by || S.name };
    this.broadcast(m);
    applyPause(m);
    this.lobby();
  },
  resume() {
    if (!S.pausedBy) return;
    this.broadcast({ t: 'resume' });
    applyResume();
    this.lobby();
  },
  kick(slot) {
    const c = this.conns.get(slot);
    if (!c) return;
    c.kicked = true;
    if (c.token) this.banned.add(c.token);
    this.send(c, { t: 'kicked' });
    setTimeout(() => { try { c.close(); } catch (e) {} this.guestLeft(c); }, 300);
  },
  setLocked(on) { S.locked = on; this.lobby(); },
  setDelay(choice) {
    S.delayChoice = choice;
    if (S.running) this.sync('delay');
    else this.lobby();
  },
  // Guest-side requests go to the host, which decides.
  request(t) {
    if (S.role === 'host') { if (t === 'pause') this.pause(); else this.resume(); }
    else this.send(this.conns.get(0), { t });
  },

  guestLeft(conn) {
    const slot = conn.slot;
    if (conn.replaced || slot === undefined || this.conns.get(slot) !== conn) return;
    this.conns.delete(slot);
    this.ready.delete(slot);
    this.rtt.delete(slot);
    S.away.delete(slot);
    const name = this.names.get(slot) || 'A player';
    if (conn.kicked) ui.toast(name + ' was removed');
    else if (conn.token) {
      // Hold the slot a while: a dropped player who comes back gets it again.
      this.reserved.set(conn.token, { slot, name, until: performance.now() + this.REJOIN_MS });
      ui.toast(name + ' disconnected - they can rejoin within 3 minutes');
    } else ui.toast(name + ' left');
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
    this.lobby();
  },

  lobby() {
    const players = [];
    for (let s = 0; s < MAX_PLAYERS; s++) if (this.names.has(s)) {
      const c = this.conns.get(s);
      players.push({
        s, name: this.names.get(s), ready: s === 0 ? !!gm : this.ready.has(s),
        rtt: Math.round(this.rtt.get(s) || 0), relay: !!(c && c.relay), away: S.away.has(s),
      });
    }
    const pause = S.pausedBy ? { f: S.stopAt, by: S.pausedBy } : null;
    this.lobbyState = { players, running: S.running, D: S.D, locked: S.locked, pause, delayChoice: S.delayChoice, autoD: this.autoDelay() };
    this.broadcast({ t: 'lobby', ...this.lobbyState });
    ui.lobby(this.lobbyState);
  },

  pickDelay() {
    if (params.get('delay')) return Math.max(1, Math.min(20, +params.get('delay')));
    if (S.delayChoice !== 'auto') return +S.delayChoice;
    return this.autoDelay();
  },
  autoDelay() {
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
      if (why === 'delay') S.D = this.pickDelay();
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
  join(code, quiet = false) {
    return new Promise((resolve, reject) => {
      S.role = 'guest';
      S.code = code;
      let done = false, welcomed = false;
      const welcome = () => { if (!done) { done = true; welcomed = true; clearTimeout(giveUp); resolve(); } };
      const fail = (why, final = false) => {
        if (done) return;
        done = true; clearTimeout(giveUp);
        if (!quiet || final) ui.error(why);
        const e = new Error(why); e.final = final; reject(e);
      };
      // First conversation to open wins; a later one is closed.
      const use = (c) => {
        if (done || this.conns.has(0)) { try { c.close(); } catch (e) {} return; }
        this.conns.set(0, c);
        c.on('data', (m) => this.fromHost(m, welcome, fail));
        c.on('close', () => {
          if (this.conns.get(0) !== c) return;
          this.conns.delete(0);
          S.running = false;
          // Only someone who was in the room tries to get back in; a refused
          // player (locked, full, wrong version) stays refused.
          if (welcomed && !S.kicked && !S.leaving) this.reconnect();
        });
        this.send(c, { t: 'hello', name: S.name, crc: ROM_CRC, token: roomToken(code) });
      };
      const NO_ROOM = 'Could not reach that room. Check the host still has the page open (not closed or asleep), or ask them for a new link.';
      let giveUp = setTimeout(() => fail(NO_ROOM), 30000);

      // 1. Direct (WebRTC via PeerJS).
      let relayStarted = false;
      const relay = () => {
        if (relayStarted || done || this.conns.has(0) || params.has('norelay')) return;
        relayStarted = true;
        if (!quiet) ui.note('Direct connection is blocked by one of your networks - connecting through the relay…');
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

  // The connection to the host dropped: keep trying to get back in. The host
  // holds our slot for three minutes (net.reserved) and syncs us back in.
  async reconnect() {
    if (this.reconnecting) return;
    this.reconnecting = true;
    ui.banner('Connection to the room lost - reconnecting…');
    const until = performance.now() + this.REJOIN_MS;
    while (performance.now() < until && !S.kicked && !S.leaving) {
      try {
        try { if (this.peer) this.peer.destroy(); } catch (e) {}
        this.peer = null;
        await this.join(S.code, true);
        if (gm) this.send(this.conns.get(0), { t: 'ready' });
        ui.banner('');
        ui.toast('Reconnected');
        this.reconnecting = false;
        return;
      } catch (e) {
        if (e.final) break;
        await sleep(3000);
      }
    }
    this.reconnecting = false;
    ui.banner('');
    if (!S.kicked) ui.error('Lost the connection to the room and could not get back in. The host may have closed it.');
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
      case 'full': onFail('That room already has four players.', true); break;
      case 'reject': onFail(m.why, true); break;
      case 'kicked':
        S.kicked = true; S.running = false;
        ui.error('The host removed you from the room.');
        break;
      case 'pause': applyPause(m); break;
      case 'resume': applyResume(); break;
      case 'lobby':
        this.lobbyState = m;
        // Catch up on a pause we missed (joined or reconnected mid-pause).
        if (m.pause && !S.pausedBy) applyPause(m.pause);
        else if (!m.pause && S.pausedBy) applyResume();
        ui.lobby(m);
        break;
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
  bars(p) {
    const el = document.createElement('span');
    const ms = p.rtt || 0, n = ms < 70 ? 4 : ms < 130 ? 3 : ms < 220 ? 2 : 1;
    el.className = 'bars' + (n === 2 ? ' mid' : n === 1 ? ' bad' : '');
    el.title = ms + ' ms' + (p.relay ? ' (through the relay)' : '');
    for (let i = 1; i <= 4; i++) {
      const b = document.createElement('i');
      b.style.height = (3 * i) + 'px';
      if (i <= n) b.className = 'on';
      el.appendChild(b);
    }
    return el;
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
      if (p && p.away) {
        const a = document.createElement('span');
        a.className = 'tag';
        a.textContent = 'away';
        a.style.flex = '0';
        li.appendChild(a);
      }
      const meta = document.createElement('i');
      if (p) meta.textContent = p.ready ? (s > 0 ? '' : 'host') : 'loading…';
      li.appendChild(meta);
      if (p && s > 0) li.appendChild(this.bars(p));
      if (p && s > 0 && S.role === 'host') {
        const k = document.createElement('button');
        k.className = 'kick';
        k.textContent = 'Kick';
        k.title = 'Remove ' + p.name + ' from the room';
        k.onclick = () => { if (confirm('Remove ' + p.name + ' from the room?')) net.kick(s); };
        li.appendChild(k);
      }
      list.appendChild(li);
    }
    const others = st.players.filter((p) => p.s !== 0);
    const allReady = st.players.every((p) => p.ready);
    const host = S.role === 'host';
    if (host) {
      $('start').hidden = st.running;
      $('start').disabled = !gm || !allReady || others.length === 0;
      $('start').textContent = others.length === 0 ? 'Waiting for friends…' : allReady ? 'Start (' + st.players.length + ' players)' : 'Waiting for everyone to load…';
    } else {
      $('start').hidden = true;
    }
    $('waitmsg').hidden = host || st.running;
    // The bar under the game.
    $('pause').hidden = !st.running;
    $('pause').textContent = st.pause ? '▶ Resume' : '⏸ Pause';
    $('lock').hidden = !host;
    $('lock').textContent = st.locked ? '🔒 Room locked' : '🔓 Room open';
    $('lock').title = st.locked ? 'New players cannot join (dropped players can still rejoin)' : 'Anyone with the link can join';
    $('delay').hidden = $('delaylbl').hidden = !host;
    if (host && document.activeElement !== $('delay')) {
      $('delay').value = st.delayChoice || 'auto';
      $('delay').options[0].textContent = 'Auto (' + (st.running && (st.delayChoice || 'auto') === 'auto' ? st.D : st.autoD) + ')';
    }
  },
  paused() {
    $('paused').hidden = !S.pausedBy;
    $('pausedmsg').textContent = 'Paused by ' + (S.pausedBy || '');
    $('pause').textContent = S.pausedBy ? '▶ Resume' : '⏸ Pause';
  },
  banner(msg) {
    $('banner').textContent = msg;
    $('banner').hidden = !msg;
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
    if (S.stalledSince && performance.now() - S.stalledSince > 400 && S.waitingOn && !S.pausedBy) {
      const players = net.lobbyState ? net.lobbyState.players : [];
      const nameOf = (s) => net.names.get(s) || (players.find((p) => p.s === s) || {}).name || 'P' + (s + 1);
      const away = S.waitingOn.filter((s) => (players.find((p) => p.s === s) || {}).away || S.away.has(s));
      w.textContent = away.length
        ? 'Waiting for ' + away.map(nameOf).join(', ') + ' - they switched to another tab or app'
        : 'Waiting for ' + S.waitingOn.map(nameOf).join(', ') + '…';
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
  $('codebox').hidden = !!code;
  const joinCode = () => {
    const c = $('codein').value.toUpperCase().replace(/[^A-Z0-9]/g, '');
    if (c.length < 4) { $('codein').focus(); return; }
    location.hash = c;                  // reloads into join mode (hashchange)
  };
  $('codego').addEventListener('click', joinCode);
  $('codein').addEventListener('keydown', (e) => { if (e.key === 'Enter') joinCode(); });
  $('own').addEventListener('click', () => {
    location.href = location.pathname + location.search;   // same page, no room code
  });
  window.addEventListener('hashchange', () => location.reload());

  const buildReady = loadBuildInfo();
  const iceReady = loadIce();
  // The page before this one kept each player's own ROM here; nothing uses it now.
  try { indexedDB.deleteDatabase('smas-battle'); } catch (e) {}

  // The password comes first: nothing else on the page shows until it has
  // opened game.bin.
  const gateMsg = (text, bad) => { $('gatemsg').textContent = text; $('gatemsg').classList.toggle('bad', !!bad); };
  gateMsg('Loading…');
  try {
    await buildReady;
  } catch (e) {
    gateMsg('Could not load the game files. Reload the page.', true);
    return;
  }
  $('version').textContent = 'build ' + BUILD.commit;
  const saved = rememberedKey();
  if (saved) {
    try { await openRom(saved); }
    catch (e) { forgetKey(); ROM = null; }
  }
  if (!ROM) {
    ui.show('gate');
    $('pw').focus();
    gateMsg('');
    await new Promise((resolve) => {
      $('gateform').addEventListener('submit', async (e) => {
        e.preventDefault();
        const pw = $('pw').value;
        if (!pw || $('unlock').disabled) return;
        $('unlock').disabled = true;
        gateMsg('Checking…');
        try {
          const raw = await deriveKey(pw);
          await openRom(raw);
          rememberKey(raw);
          resolve();
        } catch (err) {
          gateMsg(err.message === 'wrong' ? 'That is not the password.' : err.message, true);
          $('pw').select();
        }
        $('unlock').disabled = false;
      });
    });
  }
  ui.show('setup');
  autoJoin();

  $('go').addEventListener('click', go);
  // A friend who opened a room link joins as soon as the game is unlocked -
  // no second click - once this browser knows their name. The first time,
  // the name box comes first.
  function autoJoin() {
    if (code && ROM && S.name && !autoJoin.done && !params.has('nojoin')) { autoJoin.done = true; go(); }
    else if (code) $('name').focus();
  }
  async function go() {
    if (S.role) return;
    $('go').disabled = true;
    $('error').hidden = true;
    await iceReady;
    S.name = $('name').value.trim().slice(0, 16) || (code ? 'Guest' : 'Host');
    try {
      if (code) {
        await net.join(code);
      } else {
        // (The room code is not put in this page's address: reopening it
        // later would make it a guest page of a dead room.)
        await net.host();
      }
    } catch (e) {
      S.role = null;
      $('go').disabled = false;
      return;
    }
    ui.show('lobby');
    $('link').value = ui.link();
    $('roomcode').textContent = S.code;
    $('linkrow').hidden = S.role !== 'host';
    await bootEmulator();
    if (S.role === 'host') net.lobby();
    else net.send(net.conns.get(0), { t: 'ready' });
  }

  if (navigator.share) {
    $('share').hidden = false;
    $('share').addEventListener('click', () => {
      navigator.share({ title: 'SMAS Battle', text: 'Join my Mario Battle room (code ' + S.code + ')', url: ui.link() }).catch(() => {});
    });
  }
  $('pause').addEventListener('click', () => net.request(S.pausedBy ? 'resume' : 'pause'));
  $('resume').addEventListener('click', () => net.request('resume'));
  $('lock').addEventListener('click', () => net.setLocked(!S.locked));
  $('delay').addEventListener('change', () => net.setDelay($('delay').value));
  $('controls').addEventListener('click', () => {
    const e = window.EJS_emulator;
    if (e && e.controlMenu) e.controlMenu.style.display = '';
    else ui.toast('The controls open once the game has loaded');
  });
  $('full').addEventListener('click', () => {
    const el = $('stage');
    if (document.fullscreenElement) document.exitFullscreen();
    else if (el.requestFullscreen) el.requestFullscreen().catch(() => {});
  });
  $('leave').addEventListener('click', () => {
    if (S.role === 'host' && net.conns.size && !confirm('Leaving closes the room for everyone. Leave?')) return;
    S.leaving = true;
    location.href = location.pathname + location.search;
  });
  // Tell the others when this tab is hidden: the game waits for us then.
  document.addEventListener('visibilitychange', () => {
    const on = document.hidden;
    if (S.role === 'host') { if (on) S.away.add(0); else S.away.delete(0); net.lobby(); }
    else if (S.role === 'guest') net.send(net.conns.get(0), { t: 'away', on });
  });
  window.addEventListener('gamepadconnected', (e) => ui.toast('Gamepad connected: ' + (e.gamepad.id || 'controller').replace(/\s*\(.*$/, '')));

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
