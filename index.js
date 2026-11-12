const crypto = require('crypto');
const zlib = require('zlib');
const express = require('express');
const pino = require('pino');
const QRCode = require('qrcode');
const {
  default: makeWASocket,
  initAuthCreds,
  BufferJSON,
  proto,
  DisconnectReason,
  fetchLatestBaileysVersion,
  makeCacheableSignalKeyStore
} = require('@whiskeysockets/baileys');

const SETTINGS = {
  BRIDGE_KEY: '',
  WORKER_URL: 'https://pop-api-1.uuuuouuuuuuouuu.workers.dev'
};

const PORT = Number(process.env.SERVER_PORT) || Number(process.env.PORT) || 3000;
const KEY = String(process.env.BRIDGE_KEY || SETTINGS.BRIDGE_KEY || '');
const MAX_CLIENTS = Number(process.env.MAX_CLIENTS) || 10;
const IDLE_MS = 15 * 60 * 1000;
const KEEP_MS = 60 * 60 * 1000;
const ACTIVE_MS = 3 * 60 * 1000;
const TOUCH_MS = 2 * 60 * 1000;
const QR_IDLE_MS = 2 * 60 * 1000;
const QR_LIMIT = 5;
const MAX_RETRIES = 6;
const BACKOFF_MAX = 60 * 1000;
const PAUSE_MS = 30 * 60 * 1000;
const MAX_ROWS = 5000;
const MAX_TEXT = 4096;
const MAX_VALUE = 300;
const UID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/;
const PHONE_RE = /^\d{8,15}$/;
const SPEEDS = { safe: [30000, 65000], normal: [18000, 40000] };
const HOUR_CAPS = { safe: 30, normal: 45 };
const DAY_CAP = 150;
const DAY_MAX = 100000;
const REST_EVERY = [8, 15];
const REST_MS = [5 * 60 * 1000, 11 * 60 * 1000];
const RATE_PAUSE_MS = 20 * 60 * 1000;
const SETTLE_MS = 30 * 1000;
const HOLD_MS = 45 * 60 * 1000;
const WARM_COUNT = 5;
const INVALID_STREAK = 6;
const INVALID_REST = [3 * 60 * 1000, 6 * 60 * 1000];
const INVALID_MIN = 20;
const INVALID_RATIO = 0.6;
const SENT_TTL = 48 * 3600 * 1000;
const SENT_MAX = 800;
const SAVE_FAST_MS = 3000;
const SAVE_SLOW_MS = 90 * 1000;
const SNAP_BUDGET = 340000;
const SKIP = new Set(['sender-key', 'sender-key-memory']);
const SLOW = new Set(['session']);
const BLOCK_CODES = new Set([403, 463, 479]);
const BROWSER = ['POP', 'Chrome', '1.0.0'];

const logger = pino({ level: 'silent' });
const encKey = crypto.createHash('sha256').update('pop-wa:' + KEY).digest();
const linkKey = crypto.createHash('sha256').update('pop-link:' + KEY).digest();
const LINK_SKEW_MS = 60 * 1000;
const nonces = new Map();
const NONCE_RE = /^[0-9a-f]{32}$/;
const PACK_RE = /^[A-Za-z0-9+/]+={0,2}$/;
const clients = new Map();
const workerUrl = String(process.env.WORKER_URL || SETTINGS.WORKER_URL || '').replace(/\/+$/, '');
const pending = new Map();
const dropQueue = new Set();
const LOG_MAX = 400;
const outbox = new Map();

if (KEY.length < 32 || !/^https:\/\/[A-Za-z0-9.-]+$/.test(workerUrl)) {
  console.error('Set BRIDGE_KEY (32+ chars) and WORKER_URL (https) in SETTINGS at the top of index.js');
  process.exit(1);
}
let version = null;
let versionAt = 0;

function safeEqual(a, b) {
  const x = Buffer.from(String(a));
  const y = Buffer.from(String(b));
  return x.length === y.length && crypto.timingSafeEqual(x, y);
}

function ttlCache(ms) {
  const m = new Map();
  return {
    get: (k) => {
      const e = m.get(k);
      if (!e) return undefined;
      if (Date.now() > e.t) {
        m.delete(k);
        return undefined;
      }
      return e.v;
    },
    set: (k, v) => {
      if (m.size > 5000) m.clear();
      m.set(k, { v, t: Date.now() + ms });
    },
    del: (k) => {
      m.delete(k);
    },
    flushAll: () => {
      m.clear();
    }
  };
}

function boxOf(uid) {
  let b = outbox.get(uid);
  if (!b) {
    b = new Map();
    outbox.set(uid, b);
  }
  return b;
}

function prune(b) {
  const now = Date.now();
  for (const [id, e] of b) if (now - e.t > SENT_TTL) b.delete(id);
  while (b.size > SENT_MAX) b.delete(b.keys().next().value);
}

function remember(uid, sent) {
  if (!sent || !sent.key || !sent.key.id || !sent.message) return;
  const b = boxOf(uid);
  b.set(sent.key.id, { t: Date.now(), m: Buffer.from(proto.Message.encode(sent.message).finish()) });
  prune(b);
}

function recall(uid, id) {
  const b = outbox.get(uid);
  const e = b && b.get(id);
  if (!e) return undefined;
  try {
    return proto.Message.decode(e.m);
  } catch (x) {
    return undefined;
  }
}

function lock(obj, aad) {
  const iv = crypto.randomBytes(12);
  const c = crypto.createCipheriv('aes-256-gcm', linkKey, iv);
  c.setAAD(Buffer.from(aad));
  const ct = Buffer.concat([c.update(Buffer.from(JSON.stringify(obj))), c.final()]);
  return Buffer.concat([iv, ct, c.getAuthTag()]).toString('base64');
}

function unlock(text, aad) {
  const b = Buffer.from(text, 'base64');
  if (b.length < 29) throw new Error('bad');
  const d = crypto.createDecipheriv('aes-256-gcm', linkKey, b.subarray(0, 12));
  d.setAAD(Buffer.from(aad));
  d.setAuthTag(b.subarray(b.length - 16));
  const raw = Buffer.concat([d.update(b.subarray(12, b.length - 16)), d.final()]);
  return JSON.parse(raw.toString());
}

function seal(obj) {
  const raw = zlib.gzipSync(Buffer.from(JSON.stringify(obj, BufferJSON.replacer)));
  const iv = crypto.randomBytes(12);
  const c = crypto.createCipheriv('aes-256-gcm', encKey, iv);
  const ct = Buffer.concat([c.update(raw), c.final()]);
  return Buffer.concat([iv, c.getAuthTag(), ct]).toString('base64');
}

function unseal(text) {
  const b = Buffer.from(text, 'base64');
  const d = crypto.createDecipheriv('aes-256-gcm', encKey, b.subarray(0, 12));
  d.setAuthTag(b.subarray(12, 28));
  const raw = Buffer.concat([d.update(b.subarray(28)), d.final()]);
  return JSON.parse(zlib.gunzipSync(raw).toString(), BufferJSON.reviver);
}

async function worker(path, body) {
  if (!workerUrl) throw new Error('worker');
  const res = await fetch(workerUrl + path, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', 'X-Bridge-Key': KEY },
    body: JSON.stringify(body),
    signal: AbortSignal.timeout(60000)
  });
  const j = await res.json().catch(() => null);
  if (!res.ok || !j || !j.ok) throw new Error((j && j.error) || 'worker');
  return j;
}

async function waVersion() {
  if (version && Date.now() - versionAt < 6 * 3600 * 1000) return version;
  try {
    const r = await fetchLatestBaileysVersion();
    if (r && Array.isArray(r.version)) {
      version = r.version;
      versionAt = Date.now();
    }
  } catch (e) {}
  return version || undefined;
}

function makeAuth(saved, onPersist) {
  const creds = saved && saved.creds ? saved.creds : initAuthCreds();
  const keys = saved && saved.keys ? saved.keys : {};
  const store = {
    get: async (type, ids) => {
      const box = keys[type] || {};
      const out = {};
      for (const id of ids) {
        let v = box[id];
        if (v && type === 'app-state-sync-key') v = proto.Message.AppStateSyncKeyData.fromObject(v);
        if (v) out[id] = v;
      }
      return out;
    },
    set: async (data) => {
      let persist = false;
      for (const type of Object.keys(data)) {
        keys[type] = keys[type] || {};
        for (const id of Object.keys(data[type])) {
          const v = data[type][id];
          if (v) keys[type][id] = v;
          else delete keys[type][id];
        }
        if (SLOW.has(type)) persist = persist || 'slow';
        else if (!SKIP.has(type)) persist = 'fast';
      }
      if (persist) onPersist(persist === 'slow');
    }
  };
  return { creds, keys, store };
}

function snapshot(c, level) {
  const keys = {};
  for (const type of Object.keys(c.auth.keys)) {
    if (SKIP.has(type)) continue;
    if (level >= 2 && SLOW.has(type)) continue;
    keys[type] = c.auth.keys[type];
  }
  const out = [];
  if (level < 1) {
    const b = outbox.get(c.uid);
    if (b) {
      prune(b);
      for (const [id, e] of b) out.push([id, e.t, e.m]);
    }
  }
  return { creds: c.auth.creds, keys, out };
}

function restoreExtra(uid, saved) {
  if (saved && Array.isArray(saved.out)) {
    const b = boxOf(uid);
    for (const e of saved.out) {
      if (Array.isArray(e) && typeof e[0] === 'string' && Buffer.isBuffer(e[2]) && !b.has(e[0])) b.set(e[0], { t: Number(e[1]) || Date.now(), m: e[2] });
    }
    prune(b);
  }
}

function getClient(uid) {
  let c = clients.get(uid);
  if (!c) {
    c = {
      uid,
      state: 'idle',
      qr: null,
      qrCount: 0,
      phone: null,
      sock: null,
      auth: null,
      expiresAt: 0,
      job: null,
      seen: Date.now(),
      activeAt: Date.now(),
      touchedAt: 0,
      saveTimer: null,
      saveAt: 0,
      saving: null,
      openAt: 0,
      sentAt: 0,
      retries: 0,
      manual: false,
      error: null,
      log: [],
      logSeq: 0
    };
    clients.set(uid, c);
  }
  c.seen = Date.now();
  pending.delete(uid);
  return c;
}

function note(c, k, p, x) {
  if (!c || c.erased) return;
  c.logSeq++;
  c.log.push({ n: c.logSeq, t: Date.now(), k, p: p || null, x: x === undefined ? null : x });
  if (c.log.length > LOG_MAX) c.log.splice(0, c.log.length - LOG_MAX);
}

async function dropSaved(uid) {
  try {
    await worker('/bridge/session/del', { uid });
    const r = await worker('/bridge/session/get', { uid });
    if (r.found) throw new Error('left');
    dropQueue.delete(uid);
    return true;
  } catch (e) {
    dropQueue.add(uid);
    return false;
  }
}

function active(c) {
  c.seen = Date.now();
  c.activeAt = c.seen;
}

function busy(c) {
  return !!(c.job && c.job.running);
}

async function touch(c, at) {
  if (c.erased || !c.auth || !c.auth.creds.me) return;
  c.touchedAt = Date.now();
  try {
    const r = await worker('/bridge/session/touch', { uid: c.uid, at });
    if (r.expired || r.found === false) {
      if (clients.get(c.uid) === c && !busy(c) && Date.now() - c.activeAt >= KEEP_MS) {
        c.error = 'expired';
        note(c, 'expired');
        await wipe(c, true);
      }
      return;
    }
    if (r.expiresAt) c.expiresAt = Number(r.expiresAt);
  } catch (e) {}
}

function liveCount() {
  let n = 0;
  for (const c of clients.values()) if (c.sock) n++;
  return n;
}

async function save(c) {
  clearTimeout(c.saveTimer);
  c.saveTimer = null;
  c.saveAt = 0;
  if (c.erased || !c.auth || !c.auth.creds.me) return;
  let data = '';
  for (let level = 0; level < 3; level++) {
    data = seal(snapshot(c, level));
    if (data.length <= SNAP_BUDGET) break;
  }
  if (data.length > SNAP_BUDGET) return;
  const run = worker('/bridge/session/put', { uid: c.uid, data });
  c.saving = run;
  try {
    const r = await run;
    if (r.expired) {
      c.error = 'expired';
      await wipe(c, true);
      return;
    }
    if (r.expiresAt) c.expiresAt = Number(r.expiresAt);
  } catch (e) {
  } finally {
    if (c.saving === run) c.saving = null;
  }
}

function saveSoon(c, slow) {
  if (c.erased || !c.auth || !c.auth.creds.me) return;
  const at = Date.now() + (slow ? SAVE_SLOW_MS : SAVE_FAST_MS);
  if (c.saveTimer && c.saveAt <= at) return;
  clearTimeout(c.saveTimer);
  c.saveAt = at;
  c.saveTimer = setTimeout(() => {
    c.saveTimer = null;
    c.saveAt = 0;
    save(c).catch(() => {});
  }, at - Date.now());
}

async function wipe(c, logout, keep) {
  c.manual = true;
  clearTimeout(c.saveTimer);
  c.saveTimer = null;
  pending.delete(c.uid);
  if (!keep && c.job && c.job.running) c.job.stop = true;
  const sock = c.sock;
  c.sock = null;
  if (sock) {
    if (logout) {
      try {
        await sock.logout();
      } catch (e) {}
    }
    try {
      sock.end(undefined);
    } catch (e) {}
  }
  c.auth = null;
  c.state = 'idle';
  c.qr = null;
  c.phone = null;
  c.expiresAt = 0;
  c.qrCount = 0;
  c.saveAt = 0;
  outbox.delete(c.uid);
  if (c.saving) await c.saving.catch(() => {});
  const gone = await dropSaved(c.uid);
  note(c, gone ? 'wiped' : 'wipe_retry');
}

async function logoutSaved(saved) {
  const auth = makeAuth(saved, () => {});
  const sock = makeWASocket({
    version: await waVersion(),
    logger,
    auth: { creds: auth.creds, keys: makeCacheableSignalKeyStore(auth.store, logger) },
    browser: BROWSER,
    markOnlineOnConnect: false,
    syncFullHistory: false,
    shouldSyncHistoryMessage: () => false
  });
  const stop = setTimeout(() => {
    try {
      sock.end(undefined);
    } catch (e) {}
  }, 25000);
  sock.ev.on('connection.update', async (u) => {
    if (u.connection === 'open') {
      try {
        await sock.logout();
      } catch (e) {}
      clearTimeout(stop);
      try {
        sock.end(undefined);
      } catch (e) {}
    }
    if (u.qr || u.connection === 'close') {
      clearTimeout(stop);
      try {
        sock.end(undefined);
      } catch (e) {}
    }
  });
}

async function openSocket(c) {
  if (c.sock || !c.auth) return;
  c.manual = false;
  c.state = 'connecting';
  const auth = c.auth;
  const sock = makeWASocket({
    version: await waVersion(),
    logger,
    auth: { creds: auth.creds, keys: makeCacheableSignalKeyStore(auth.store, logger) },
    browser: BROWSER,
    markOnlineOnConnect: false,
    syncFullHistory: false,
    shouldSyncHistoryMessage: () => false,
    generateHighQualityLinkPreview: false,
    connectTimeoutMs: 60000,
    defaultQueryTimeoutMs: 90000,
    keepAliveIntervalMs: 25000,
    retryRequestDelayMs: 350,
    maxMsgRetryCount: 5,
    msgRetryCounterCache: c.retryCache || (c.retryCache = ttlCache(3600 * 1000)),
    userDevicesCache: c.devCache || (c.devCache = ttlCache(5 * 60 * 1000)),
    getMessage: async (key) => {
      const m = key && key.id ? recall(c.uid, key.id) : undefined;
      if (m) note(c, 'resent');
      return m;
    }
  });
  if (c.auth !== auth || c.sock) {
    try {
      sock.end(undefined);
    } catch (e) {}
    return;
  }
  c.sock = sock;
  sock.ev.on('creds.update', () => saveSoon(c));
  sock.ev.on('messages.update', (list) => {
    const j = c.job;
    if (!j || !j.ids) return;
    for (const u of list || []) {
      const id = u && u.key && u.key.id;
      const st = u && u.update ? Number(u.update.status) : 0;
      if (id && st >= 3 && j.ids.has(id) && !j.got.has(id)) {
        j.got.add(id);
        j.delivered++;
      }
    }
  });
  sock.ev.on('connection.update', async (u) => {
    if (c.sock !== sock) return;
    if (u.qr) {
      c.qrCount++;
      if (c.qrCount > QR_LIMIT) {
        c.manual = true;
        c.error = 'qr_timeout';
        note(c, 'qr_timeout');
        c.sock = null;
        c.auth = null;
        c.state = 'idle';
        c.qr = null;
        try {
          sock.end(undefined);
        } catch (e) {}
        return;
      }
      try {
        c.qr = await QRCode.toDataURL(u.qr, { margin: 1, width: 300, errorCorrectionLevel: 'M' });
        if (c.sock === sock) {
          c.state = 'qr';
          note(c, 'qr', null, c.qrCount);
        }
      } catch (e) {}
    }
    if (u.connection === 'open') {
      c.state = 'open';
      c.qr = null;
      c.qrCount = 0;
      c.retries = 0;
      c.error = null;
      c.openAt = Date.now();
      c.phone = String((sock.user && sock.user.id) || '').split(':')[0].split('@')[0] || null;
      note(c, 'open', c.phone);
      await save(c);
    }
    if (u.connection === 'close') {
      const err = u.lastDisconnect && u.lastDisconnect.error;
      const code = err && err.output ? err.output.statusCode : 0;
      c.sock = null;
      if (c.manual) {
        c.state = 'idle';
        return;
      }
      if (code === DisconnectReason.loggedOut) {
        c.error = 'logged_out';
        note(c, 'logged_out');
        await wipe(c, false, true);
        return;
      }
      if (code === DisconnectReason.forbidden) {
        c.state = 'idle';
        c.error = 'restricted';
        note(c, 'restricted');
        if (c.job && c.job.running) c.job.block = true;
        await save(c).catch(() => {});
        return;
      }
      if (code === DisconnectReason.connectionReplaced) {
        c.state = 'idle';
        c.error = 'replaced';
        note(c, 'replaced');
        return;
      }
      const linked = !!(c.auth && c.auth.creds.me);
      if (c.auth && (linked || c.retries < MAX_RETRIES)) {
        c.retries++;
        c.state = 'connecting';
        note(c, 'reconnect', null, c.retries);
        const ms = code === DisconnectReason.restartRequired ? 500 : Math.min(2000 * c.retries, BACKOFF_MAX);
        setTimeout(() => {
          if (!c.sock && c.auth && clients.get(c.uid) === c && !c.manual) openSocket(c).catch(() => {});
        }, ms);
      } else {
        c.state = 'idle';
        c.error = 'failed';
        note(c, 'conn_failed');
      }
    }
  });
}

async function start(c, mode) {
  if (c.sock) return;
  if (liveCount() >= MAX_CLIENTS) {
    c.error = 'busy';
    return;
  }
  if (!c.auth) {
    const r = await worker('/bridge/session/get', { uid: c.uid });
    if (r.found && r.data) {
      let saved = null;
      try {
        saved = unseal(r.data);
      } catch (e) {
        await dropSaved(c.uid);
      }
      if (saved && r.expired) {
        c.error = 'expired';
        logoutSaved(saved).catch(() => {});
        const gone = await dropSaved(c.uid);
        note(c, 'expired');
        note(c, gone ? 'wiped' : 'wipe_retry');
      } else if (saved) {
        restoreExtra(c.uid, saved);
        c.auth = makeAuth(saved, (slow) => saveSoon(c, slow));
        c.expiresAt = Number(r.expiresAt) || 0;
        note(c, 'resume');
      }
    }
    if (!c.auth) {
      if (mode !== 'new') return;
      c.auth = makeAuth(null, (slow) => saveSoon(c, slow));
      c.expiresAt = 0;
    }
  }
  c.retries = 0;
  c.error = null;
  await openSocket(c);
}

function spin(text) {
  let out = text;
  for (let k = 0; k < 4; k++) {
    const next = out.replace(/\{([^{}]*\|[^{}]*)\}/g, (m, body) => {
      const parts = body.split('|');
      return parts[Math.floor(Math.random() * parts.length)];
    });
    if (next === out) break;
    out = next;
  }
  return out;
}

function fill(template, defs, values) {
  return spin(template).replace(/\{\{([1-6])\}\}/g, (m, n) => {
    const i = Number(n) - 1;
    const v = values && typeof values[i] === 'string' && values[i] !== '' ? values[i] : defs[i];
    return typeof v === 'string' ? v : '';
  });
}

function wait(job, ms) {
  return new Promise((resolve) => {
    const end = Date.now() + ms;
    const tick = () => {
      if (job.stop || job.block || Date.now() >= end) resolve();
      else setTimeout(tick, Math.min(500, end - Date.now()));
    };
    tick();
  });
}

async function ready(c, job) {
  if (c.state === 'open' && c.sock) return true;
  const end = Date.now() + PAUSE_MS;
  job.paused = true;
  note(c, 'paused');
  while (Date.now() < end && !job.stop && !job.block) {
    active(c);
    if (c.state === 'open' && c.sock) {
      job.paused = false;
      note(c, 'resumed', null, job.done);
      return true;
    }
    if (c.error === 'restricted' || c.error === 'replaced') break;
    await wait(job, 1000);
  }
  job.paused = false;
  return false;
}

function pick(r) {
  return r[0] + Math.floor(Math.random() * (r[1] - r[0]));
}

async function typeLike(c, jid, text) {
  try {
    await c.sock.sendPresenceUpdate('composing', jid);
    await new Promise((r) => setTimeout(r, Math.min(9000, 2000 + text.length * 45 + Math.floor(Math.random() * 1500))));
    await c.sock.sendPresenceUpdate('paused', jid);
    await new Promise((r) => setTimeout(r, 300 + Math.floor(Math.random() * 900)));
  } catch (e) {}
}

function skipRest(job, from, total) {
  for (let k = from; k < total; k++) push(job, k, 'k');
}

async function runJob(c, job, input) {
  const range = SPEEDS[input.speed] || SPEEDS.safe;
  const hourCap = HOUR_CAPS[input.speed] || HOUR_CAPS.safe;
  let streak = 0;
  let nextRest = pick(REST_EVERY);
  let rateHits = 0;
  let badRun = 0;
  let checked = 0;
  let invalid = 0;
  const stamps = [];
  const settle = SETTLE_MS - (Date.now() - c.openAt);
  if (settle > 0) {
    note(c, 'settle', null, Math.ceil(settle / 1000));
    await wait(job, settle);
  }
  for (let i = 0; i < input.rows.length; i++) {
    if (job.stop) break;
    active(c);
    if (job.block) {
      skipRest(job, i, input.rows.length);
      return;
    }
    if (!(await ready(c, job))) {
      if (job.stop) break;
      note(c, job.block || c.error === 'restricted' ? 'restricted_stop' : 'lost');
      skipRest(job, i, input.rows.length);
      return;
    }
    if (job.sent >= input.dayLeft) {
      note(c, 'day_cap', null, input.dayCap);
      skipRest(job, i, input.rows.length);
      return;
    }
    const row = input.rows[i];
    let status = 'f';
    let retry = false;
    let why = null;
    try {
      const hits = await c.sock.onWhatsApp(row.p);
      const hit = hits && hits[0];
      checked++;
      if (!hit || !hit.exists) {
        status = 'n';
        invalid++;
      } else {
        const text = fill(input.template, input.defs, row.v);
        await typeLike(c, hit.jid, text);
        if (job.stop || !c.sock) throw new Error('connection closed');
        const sent = await c.sock.sendMessage(hit.jid, { text });
        remember(c.uid, sent);
        if (sent && sent.key && sent.key.id) job.ids.add(sent.key.id);
        saveSoon(c, true);
        status = 's';
        c.sentAt = Date.now();
        stamps.push(Date.now());
      }
    } catch (e) {
      status = 'f';
      why = reason(e);
      if (why === 'conn' && (row.t || 0) < 3 && !job.stop) {
        row.t = (row.t || 0) + 1;
        retry = true;
      }
    }
    if (why === 'blocked') {
      job.block = true;
      c.error = 'restricted';
      note(c, 'restricted_stop');
      skipRest(job, i, input.rows.length);
      return;
    }
    if (why === 'rate' && !job.stop) {
      rateHits++;
      if (rateHits >= 2) {
        note(c, 'rate_stop');
        skipRest(job, i, input.rows.length);
        return;
      }
      note(c, 'rate_pause', null, Math.round(RATE_PAUSE_MS / 60000));
      await wait(job, RATE_PAUSE_MS);
      i--;
      continue;
    }
    if (retry) {
      await wait(job, 3000);
      i--;
      continue;
    }
    push(job, i, status);
    note(c, status === 's' ? 'sent' : status === 'n' ? 'not_wa' : 'failed', row.p, why);
    badRun = status === 'n' ? badRun + 1 : 0;
    if (checked >= INVALID_MIN && invalid / checked > INVALID_RATIO) {
      note(c, 'invalid_stop');
      skipRest(job, i + 1, input.rows.length);
      return;
    }
    if (i < input.rows.length - 1 && !job.stop) {
      while (stamps.length && Date.now() - stamps[0] > 3600000) stamps.shift();
      let ms;
      if (status !== 's') {
        ms = pick([4000, 9000]);
        if (badRun >= INVALID_STREAK) {
          badRun = 0;
          ms = pick(INVALID_REST);
          note(c, 'invalid_rest', null, Math.round(ms / 60000));
        }
        await wait(job, ms);
        continue;
      }
      streak++;
      ms = pick(range);
      if (job.sent <= WARM_COUNT) ms = Math.round(ms * 1.5);
      if (Math.random() < 0.1) ms = Math.round(ms * 2);
      if (stamps.length >= hourCap) {
        ms = Math.max(ms, 3600000 - (Date.now() - stamps[0]) + pick([20000, 90000]));
        note(c, 'cap', null, [hourCap, Math.round(ms / 60000)]);
      } else if (streak >= nextRest) {
        streak = 0;
        nextRest = pick(REST_EVERY);
        ms = pick(REST_MS);
        note(c, 'rest', null, Math.round(ms / 60000));
      } else note(c, 'wait', null, Math.round(ms / 1000));
      await wait(job, ms);
    }
  }
}

function reason(e) {
  const code = e && e.output ? e.output.statusCode : Number(e && (e.status || e.code)) || 0;
  const data = e && e.data && (e.data.attrs || e.data);
  const ack = data ? Number(data.code || data.error) || 0 : 0;
  const m = String((e && e.message) || '').toLowerCase();
  if (BLOCK_CODES.has(code) || BLOCK_CODES.has(ack) || m.includes('restrict') || m.includes('forbidden') || m.includes('banned')) return 'blocked';
  if (code === 429 || m.includes('rate')) return 'rate';
  if (m.includes('timed out') || m.includes('timeout')) return 'timeout';
  if (m.includes('closed') || m.includes('connection')) return 'conn';
  return 'other';
}

function push(job, i, status) {
  job.results.push([i, status]);
  job.done++;
  if (status === 's') job.sent++;
  else if (status === 'n') job.invalid++;
  else if (status === 'k') job.skipped++;
  else job.failed++;
}

function cleanInput(b) {
  const template = typeof b.template === 'string' ? b.template : '';
  if (!template.trim() || template.length > MAX_TEXT) return null;
  const defs = Array.isArray(b.defs) ? b.defs : [];
  if (defs.length > 6 || defs.some((d) => typeof d !== 'string' || d.length > MAX_VALUE)) return null;
  const rows = Array.isArray(b.rows) ? b.rows : [];
  if (!rows.length || rows.length > MAX_ROWS) return null;
  const cap = Number.isInteger(b.dayCap) && b.dayCap >= 0 ? (b.dayCap === 0 ? DAY_MAX : Math.min(b.dayCap, DAY_MAX)) : DAY_CAP;
  const used = Number.isInteger(b.dayUsed) && b.dayUsed >= 0 ? Math.min(b.dayUsed, cap) : 0;
  for (const r of rows) {
    if (!r || typeof r.p !== 'string' || !PHONE_RE.test(r.p)) return null;
    if (!Array.isArray(r.v) || r.v.length > 6 || r.v.some((x) => typeof x !== 'string' || x.length > MAX_VALUE)) return null;
  }
  return { template, defs, rows: rows.map((r) => ({ p: r.p, v: r.v })), speed: b.speed === 'normal' ? 'normal' : 'safe', dayCap: cap, dayLeft: cap - used };
}

function view(c, from, lf) {
  const j = c && c.job;
  return {
    ok: true,
    state: c ? c.state : 'idle',
    qr: c && c.state === 'qr' ? c.qr : null,
    phone: c && c.state === 'open' ? c.phone : null,
    error: c ? c.error : null,
    logSeq: c ? c.logSeq : 0,
    log: c ? c.log.filter((e) => e.n > (Number(lf) || 0)) : [],
    job: j
      ? {
          id: j.id,
          total: j.total,
          done: j.done,
          sent: j.sent,
          invalid: j.invalid,
          failed: j.failed,
          skipped: j.skipped,
          delivered: j.delivered,
          running: j.running,
          stopped: j.stop,
          paused: !!j.paused,
          results: j.results.slice(Math.max(0, Number(from) || 0))
        }
      : null
  };
}

async function expirePending(uid) {
  pending.delete(uid);
  try {
    const r = await worker('/bridge/session/get', { uid });
    if (r.found && r.data) {
      if (!r.expired) {
        pending.set(uid, Number(r.expiresAt) || Date.now() + KEEP_MS);
        return;
      }
      try {
        logoutSaved(unseal(r.data)).catch(() => {});
      } catch (e) {}
    }
    await dropSaved(uid);
  } catch (e) {
    pending.set(uid, Date.now() + 60000);
  }
}

setInterval(() => {
  const now = Date.now();
  for (const uid of dropQueue) dropSaved(uid).catch(() => {});
  for (const [uid, at] of pending) {
    if (now >= at && !clients.has(uid)) expirePending(uid).catch(() => {});
  }
  for (const c of clients.values()) {
    if (busy(c)) {
      c.activeAt = now;
      c.seen = now;
    }
    const linked = !!(c.auth && c.auth.creds.me);
    const live = now - c.activeAt < ACTIVE_MS;
    if (linked && live && now - c.touchedAt > TOUCH_MS) touch(c, now).catch(() => {});
    if (busy(c)) continue;
    const pairing = c.sock && c.state !== 'open' && !linked;
    if (pairing && now - c.seen > QR_IDLE_MS) {
      c.manual = true;
      const s = c.sock;
      c.sock = null;
      c.auth = null;
      c.state = 'idle';
      c.qr = null;
      try {
        s.end(undefined);
      } catch (e) {}
      continue;
    }
    if (linked && now - c.activeAt >= KEEP_MS) {
      c.error = 'expired';
      note(c, 'expired');
      wipe(c, true).catch(() => {});
      continue;
    }
    const holding = linked && c.sock && now - c.sentAt < HOLD_MS;
    if (now - c.seen > IDLE_MS && !holding) {
      c.manual = true;
      const s = c.sock;
      c.sock = null;
      const finish = () => {
        try {
          if (s) s.end(undefined);
        } catch (e) {}
      };
      clients.delete(c.uid);
      if (linked) {
        const deadline = c.activeAt + KEEP_MS;
        pending.set(c.uid, deadline);
        save(c)
          .then(() => worker('/bridge/session/touch', { uid: c.uid, at: c.activeAt }))
          .catch(() => {})
          .finally(finish);
      } else finish();
    }
  }
}, 30000).unref();

setInterval(() => {
  const now = Date.now();
  for (const [n, at] of nonces) if (now - at > LINK_SKEW_MS * 2) nonces.delete(n);
}, 30000).unref();

const ROUTES = new Set(['/health', '/status', '/connect', '/send', '/stop', '/logout']);

function deny(req, res) {
  req.socket.destroy();
}

const app = express();
app.disable('x-powered-by');
app.disable('etag');
app.set('trust proxy', false);

app.use((req, res, next) => {
  if (req.method !== 'POST' || !ROUTES.has(req.path) || Object.keys(req.query).length) return deny(req, res);
  const type = String(req.get('content-type') || '').toLowerCase();
  if (!type.startsWith('application/json')) return deny(req, res);
  const t = Number(req.get('x-link-time'));
  const n = String(req.get('x-link-nonce') || '');
  if (!Number.isFinite(t) || Math.abs(Date.now() - t) > LINK_SKEW_MS || !NONCE_RE.test(n) || nonces.has(n)) return deny(req, res);
  req.linkTime = t;
  req.linkNonce = n;
  res.set('Cache-Control', 'no-store');
  res.set('X-Content-Type-Options', 'nosniff');
  next();
});

app.use(express.json({ limit: '6mb', strict: true }));

app.use((err, req, res, next) => {
  deny(req, res);
});

app.use((req, res, next) => {
  const pack = req.body && req.body.d;
  if (typeof pack !== 'string' || !PACK_RE.test(pack)) return deny(req, res);
  let body;
  try {
    body = unlock(pack, req.path + '.' + req.linkTime + '.' + req.linkNonce);
  } catch (e) {
    return deny(req, res);
  }
  if (!body || typeof body !== 'object' || typeof body.uid !== 'string' || !UID_RE.test(body.uid)) return deny(req, res);
  nonces.set(req.linkNonce, Date.now());
  req.body = body;
  const aad = 'res.' + req.linkNonce;
  const send = res.json.bind(res);
  res.json = (obj) => send({ d: lock(obj, aad) });
  next();
});

app.post('/health', (req, res) => {
  res.json({ ok: true, clients: clients.size });
});

app.post('/status', (req, res) => {
  const c = clients.get(req.body.uid);
  if (c) active(c);
  res.json(view(c, req.body.from, req.body.lf));
});

app.post('/connect', async (req, res) => {
  const c = getClient(req.body.uid);
  active(c);
  const mode = req.body.mode === 'new' ? 'new' : 'resume';
  if (mode === 'new') c.qrCount = 0;
  try {
    await start(c, mode);
  } catch (e) {
    return res.status(502).json({ ok: false, error: 'unavailable' });
  }
  if (c.error === 'busy') {
    c.error = null;
    return res.status(503).json({ ok: false, error: 'busy' });
  }
  res.json(view(c, 0, req.body.lf));
});

app.post('/send', (req, res) => {
  const c = clients.get(req.body.uid);
  if (c) active(c);
  if (!c || c.state !== 'open' || !c.sock) return res.status(409).json({ ok: false, error: c && c.error === 'restricted' ? 'restricted' : 'not_open' });
  if (c.job && c.job.running) return res.status(409).json({ ok: false, error: 'job_running' });
  const input = cleanInput(req.body);
  if (!input) return res.status(400).json({ ok: false, error: 'bad' });
  if (input.dayLeft <= 0) return res.status(429).json({ ok: false, error: 'day_cap' });
  const job = {
    id: crypto.randomUUID(),
    total: input.rows.length,
    done: 0,
    sent: 0,
    invalid: 0,
    failed: 0,
    skipped: 0,
    delivered: 0,
    ids: new Set(),
    got: new Set(),
    block: false,
    results: [],
    running: true,
    paused: false,
    stop: false
  };
  c.job = job;
  note(c, 'start', null, job.total);
  c.runningJob = runJob(c, job, input)
    .catch(() => {})
    .finally(() => {
      job.running = false;
      if (c.erased) {
        input.rows.length = 0;
        input.defs.length = 0;
        input.template = '';
        job.results.length = 0;
        job.ids.clear();
        job.got.clear();
      }
      note(c, job.stop ? 'stopped' : 'done', null, [job.sent, job.invalid, job.failed + job.skipped]);
      save(c).catch(() => {});
    });
  res.json(view(c, 0, req.body.lf));
});

app.post('/stop', (req, res) => {
  const c = clients.get(req.body.uid);
  if (c && c.job && c.job.running && !c.job.stop) {
    c.job.stop = true;
    note(c, 'stopping');
  }
  res.json(view(c, req.body.from, req.body.lf));
});

app.post('/logout', async (req, res) => {
  const c = getClient(req.body.uid);
  if (req.body.purge === true) c.erased = true;
  try {
    if (c.auth || (req.body.purge === true && c.sock)) {
      await wipe(c, true);
    } else {
      const r = await worker('/bridge/session/get', { uid: c.uid });
      if (r.found && r.data) {
        try {
          logoutSaved(unseal(r.data)).catch(() => {});
        } catch (e) {}
      }
      const gone = await dropSaved(c.uid);
      note(c, gone ? 'wiped' : 'wipe_retry');
    }
  } catch (e) {
    return res.status(502).json({ ok: false, error: 'unavailable' });
  }
  if (req.body.purge === true) {
    if (!await dropSaved(c.uid)) return res.status(502).json({ ok: false, error: 'unavailable' });
    if (c.job) c.job.stop = true;
    if (c.runningJob) await c.runningJob.catch(() => {});
    c.erased = true;
    if (c.job) { c.job.stop = true; c.job.results.length = 0; c.job.ids.clear(); }
    clearTimeout(c.saveTimer);
    c.auth = null;
    c.qr = null;
    c.phone = null;
    c.log.length = 0;
    c.job = null;
    pending.delete(c.uid);
    outbox.delete(c.uid);
    clients.delete(c.uid);
    return res.json({ ok: true, deleted: true });
  }
  c.error = null;
  res.json(view(c, 0, req.body.lf));
});

app.use((req, res) => {
  deny(req, res);
});

const server = app.listen(PORT, '0.0.0.0', () => {
  console.log('POP bridge ready on port ' + PORT);
});
server.headersTimeout = 15000;
server.requestTimeout = 30000;
server.keepAliveTimeout = 5000;

process.on('unhandledRejection', () => {});
process.on('uncaughtException', (e) => {
  console.error('error', e && e.message);
});
