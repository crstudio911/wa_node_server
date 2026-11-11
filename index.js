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

const PORT = Number(process.env.PORT) || 3000;
const KEY = String(process.env.BRIDGE_KEY || '');
const MAX_CLIENTS = Number(process.env.MAX_CLIENTS) || 10;
const IDLE_MS = 15 * 60 * 1000;
const KEEP_MS = 60 * 60 * 1000;
const ACTIVE_MS = 3 * 60 * 1000;
const TOUCH_MS = 2 * 60 * 1000;
const QR_IDLE_MS = 2 * 60 * 1000;
const QR_LIMIT = 5;
const MAX_RETRIES = 6;
const MAX_ROWS = 500;
const MAX_TEXT = 4096;
const MAX_VALUE = 300;
const UID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/;
const PHONE_RE = /^\d{8,15}$/;
const SPEEDS = { safe: [8000, 15000], normal: [4000, 8000] };
const SKIP = new Set(['session', 'sender-key', 'sender-key-memory']);
const BROWSER = ['POP', 'Chrome', '1.0.0'];

const logger = pino({ level: 'silent' });
const encKey = crypto.createHash('sha256').update('pop-wa:' + KEY).digest();
const clients = new Map();
const workerUrl = String(process.env.WORKER_URL || '').replace(/\/+$/, '');
const pending = new Map();

if (KEY.length < 32 || !/^https:\/\/[A-Za-z0-9.-]+$/.test(workerUrl)) {
  console.error('BRIDGE_KEY (32+ chars) and WORKER_URL (https) are required');
  process.exit(1);
}
let version = null;
let versionAt = 0;

function safeEqual(a, b) {
  const x = Buffer.from(String(a));
  const y = Buffer.from(String(b));
  return x.length === y.length && crypto.timingSafeEqual(x, y);
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
    signal: AbortSignal.timeout(30000)
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
        if (!SKIP.has(type)) persist = true;
      }
      if (persist) onPersist();
    }
  };
  return { creds, keys, store };
}

function snapshot(auth) {
  const keys = {};
  for (const type of Object.keys(auth.keys)) {
    if (!SKIP.has(type)) keys[type] = auth.keys[type];
  }
  return { creds: auth.creds, keys };
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
      saving: null,
      retries: 0,
      manual: false,
      error: null
    };
    clients.set(uid, c);
  }
  c.seen = Date.now();
  pending.delete(uid);
  return c;
}

function active(c) {
  c.seen = Date.now();
  c.activeAt = c.seen;
}

function busy(c) {
  return !!(c.job && c.job.running);
}

async function touch(c, at) {
  if (!c.auth || !c.auth.creds.me) return;
  c.touchedAt = Date.now();
  try {
    const r = await worker('/bridge/session/touch', { uid: c.uid, at });
    if (r.expired || r.found === false) {
      if (clients.get(c.uid) === c && !busy(c) && Date.now() - c.activeAt >= KEEP_MS) {
        c.error = 'expired';
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
  if (!c.auth || !c.auth.creds.me) return;
  const data = seal(snapshot(c.auth));
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

function saveSoon(c) {
  if (c.saveTimer || !c.auth || !c.auth.creds.me) return;
  c.saveTimer = setTimeout(() => {
    c.saveTimer = null;
    save(c).catch(() => {});
  }, 3000);
}

async function wipe(c, logout) {
  c.manual = true;
  clearTimeout(c.saveTimer);
  c.saveTimer = null;
  pending.delete(c.uid);
  if (c.job && c.job.running) c.job.stop = true;
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
  if (c.saving) await c.saving.catch(() => {});
  await worker('/bridge/session/del', { uid: c.uid }).catch(() => {});
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
    connectTimeoutMs: 30000
  });
  if (c.auth !== auth || c.sock) {
    try {
      sock.end(undefined);
    } catch (e) {}
    return;
  }
  c.sock = sock;
  sock.ev.on('creds.update', () => saveSoon(c));
  sock.ev.on('connection.update', async (u) => {
    if (c.sock !== sock) return;
    if (u.qr) {
      c.qrCount++;
      if (c.qrCount > QR_LIMIT) {
        c.manual = true;
        c.error = 'qr_timeout';
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
        if (c.sock === sock) c.state = 'qr';
      } catch (e) {}
    }
    if (u.connection === 'open') {
      c.state = 'open';
      c.qr = null;
      c.qrCount = 0;
      c.retries = 0;
      c.error = null;
      c.phone = String((sock.user && sock.user.id) || '').split(':')[0].split('@')[0] || null;
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
        await wipe(c, false);
        return;
      }
      if (c.retries < MAX_RETRIES && c.auth) {
        c.retries++;
        c.state = 'connecting';
        setTimeout(() => {
          if (!c.sock && c.auth && clients.get(c.uid) === c && !c.manual) openSocket(c).catch(() => {});
        }, Math.min(2000 * c.retries, 10000));
      } else {
        c.state = 'idle';
        c.error = 'failed';
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
        await worker('/bridge/session/del', { uid: c.uid }).catch(() => {});
      }
      if (saved && r.expired) {
        c.error = 'expired';
        logoutSaved(saved).catch(() => {});
      } else if (saved) {
        c.auth = makeAuth(saved, () => saveSoon(c));
        c.expiresAt = Number(r.expiresAt) || 0;
      }
    }
    if (!c.auth) {
      if (mode !== 'new') return;
      c.auth = makeAuth(null, () => saveSoon(c));
      c.expiresAt = 0;
    }
  }
  c.retries = 0;
  c.error = null;
  await openSocket(c);
}

function fill(template, defs, values) {
  return template.replace(/\{\{([1-6])\}\}/g, (m, n) => {
    const i = Number(n) - 1;
    const v = values && typeof values[i] === 'string' && values[i] !== '' ? values[i] : defs[i];
    return typeof v === 'string' ? v : '';
  });
}

function wait(job, ms) {
  return new Promise((resolve) => {
    const end = Date.now() + ms;
    const tick = () => {
      if (job.stop || Date.now() >= end) resolve();
      else setTimeout(tick, Math.min(500, end - Date.now()));
    };
    tick();
  });
}

async function ready(c, job) {
  const end = Date.now() + 60000;
  while (Date.now() < end) {
    if (job.stop) return false;
    if (c.state === 'open' && c.sock) return true;
    if (!c.auth) return false;
    await wait(job, 1000);
  }
  return false;
}

async function runJob(c, job, input) {
  const range = SPEEDS[input.speed] || SPEEDS.safe;
  for (let i = 0; i < input.rows.length; i++) {
    if (job.stop) break;
    active(c);
    if (!(await ready(c, job))) {
      if (job.stop) break;
      for (let k = i; k < input.rows.length; k++) push(job, k, 'f');
      return;
    }
    const row = input.rows[i];
    let status = 'f';
    try {
      const hits = await c.sock.onWhatsApp(row.p);
      const hit = hits && hits[0];
      if (!hit || !hit.exists) status = 'n';
      else {
        await c.sock.sendMessage(hit.jid, { text: fill(input.template, input.defs, row.v) });
        status = 's';
      }
    } catch (e) {
      status = 'f';
    }
    push(job, i, status);
    if (i < input.rows.length - 1 && !job.stop) await wait(job, range[0] + Math.floor(Math.random() * (range[1] - range[0])));
  }
}

function push(job, i, status) {
  job.results.push([i, status]);
  job.done++;
  if (status === 's') job.sent++;
  else if (status === 'n') job.invalid++;
  else job.failed++;
}

function cleanInput(b) {
  const template = typeof b.template === 'string' ? b.template : '';
  if (!template.trim() || template.length > MAX_TEXT) return null;
  const defs = Array.isArray(b.defs) ? b.defs : [];
  if (defs.length > 6 || defs.some((d) => typeof d !== 'string' || d.length > MAX_VALUE)) return null;
  const rows = Array.isArray(b.rows) ? b.rows : [];
  if (!rows.length || rows.length > MAX_ROWS) return null;
  for (const r of rows) {
    if (!r || typeof r.p !== 'string' || !PHONE_RE.test(r.p)) return null;
    if (!Array.isArray(r.v) || r.v.length > 6 || r.v.some((x) => typeof x !== 'string' || x.length > MAX_VALUE)) return null;
  }
  return { template, defs, rows: rows.map((r) => ({ p: r.p, v: r.v })), speed: b.speed === 'normal' ? 'normal' : 'safe' };
}

function view(c, from) {
  const j = c && c.job;
  return {
    ok: true,
    state: c ? c.state : 'idle',
    qr: c && c.state === 'qr' ? c.qr : null,
    phone: c && c.state === 'open' ? c.phone : null,
    error: c ? c.error : null,
    job: j
      ? {
          id: j.id,
          total: j.total,
          done: j.done,
          sent: j.sent,
          invalid: j.invalid,
          failed: j.failed,
          running: j.running,
          stopped: j.stop,
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
    await worker('/bridge/session/del', { uid });
  } catch (e) {
    pending.set(uid, Date.now() + 60000);
  }
}

setInterval(() => {
  const now = Date.now();
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
      wipe(c, true).catch(() => {});
      continue;
    }
    if (now - c.seen > IDLE_MS) {
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

const app = express();
app.disable('x-powered-by');
app.set('trust proxy', 1);
app.use((req, res, next) => {
  res.set('Cache-Control', 'no-store');
  res.set('X-Content-Type-Options', 'nosniff');
  next();
});
app.use(express.json({ limit: '1mb' }));

app.get('/', (req, res) => {
  res.json({ ok: true });
});

app.use((req, res, next) => {
  if (!safeEqual(req.get('x-bridge-key') || '', KEY)) return res.status(403).json({ ok: false, error: 'forbidden' });
  const uid = req.body && req.body.uid;
  if (typeof uid !== 'string' || !UID_RE.test(uid)) return res.status(400).json({ ok: false, error: 'bad' });
  next();
});

app.post('/status', (req, res) => {
  const c = clients.get(req.body.uid);
  if (c) active(c);
  res.json(view(c, req.body.from));
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
  res.json(view(c, 0));
});

app.post('/send', (req, res) => {
  const c = clients.get(req.body.uid);
  if (c) active(c);
  if (!c || c.state !== 'open' || !c.sock) return res.status(409).json({ ok: false, error: 'not_open' });
  if (c.job && c.job.running) return res.status(409).json({ ok: false, error: 'job_running' });
  const input = cleanInput(req.body);
  if (!input) return res.status(400).json({ ok: false, error: 'bad' });
  const job = {
    id: crypto.randomUUID(),
    total: input.rows.length,
    done: 0,
    sent: 0,
    invalid: 0,
    failed: 0,
    results: [],
    running: true,
    stop: false
  };
  c.job = job;
  runJob(c, job, input)
    .catch(() => {})
    .finally(() => {
      job.running = false;
    });
  res.json(view(c, 0));
});

app.post('/stop', (req, res) => {
  const c = clients.get(req.body.uid);
  if (c && c.job && c.job.running) c.job.stop = true;
  res.json(view(c, req.body.from));
});

app.post('/logout', async (req, res) => {
  const c = getClient(req.body.uid);
  try {
    if (c.auth) {
      await wipe(c, true);
    } else {
      const r = await worker('/bridge/session/get', { uid: c.uid });
      if (r.found && r.data) {
        try {
          logoutSaved(unseal(r.data)).catch(() => {});
        } catch (e) {}
      }
      await worker('/bridge/session/del', { uid: c.uid });
    }
  } catch (e) {
    return res.status(502).json({ ok: false, error: 'unavailable' });
  }
  c.error = null;
  res.json(view(c, 0));
});

app.use((req, res) => {
  res.status(404).json({ ok: false, error: 'not_found' });
});

app.listen(PORT, () => {
  console.log('POP bridge on ' + PORT);
});
