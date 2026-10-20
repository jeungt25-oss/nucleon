const express = require('express');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const net = require('net');
const { spawn } = require('child_process');
const { pipeline } = require('stream/promises');
const { Readable } = require('stream');

/* ---------- config ---------- */
const WEB_PORT = process.env.PORT || 3000;
const BASE_MC_PORT = 25565;
const BASE_BEDROCK_PORT = 19132;
const MAX_SERVERS_PER_USER = 3;
const MAX_BACKUPS = 3;
const MAX_SUBUSERS = 5;
const RAM = '1G';
const SOFT_ORDER = ['Paper', 'Purpur', 'Fabric', 'Vanilla'];
const PLUGIN_SOFT = ['Paper', 'Purpur'];
const MIN_VER = '1.16.5';
const FALLBACK_VERS = ['1.21.4', '1.21.1', '1.20.6', '1.20.4', '1.19.4', '1.18.2'];
const UA = { 'User-Agent': 'Nucleon/1.0 (Creed Inc.)' };

/* custom address settings */
const DOMAIN = process.env.DOMAIN || 'nucleon.host';
const RESERVED = ['www', 'api', 'admin', 'mail', 'play', 'panel', 'dashboard', 'ftp', 'ns1', 'ns2', 'root', 'support'];
const CF_TOKEN = process.env.CF_TOKEN || '';
const CF_ZONE = process.env.CF_ZONE || '';
const SRV_TARGET = process.env.SRV_TARGET || 'play.' + DOMAIN;

const DATA = path.join(__dirname, 'data');
const SRV = path.join(__dirname, 'servers');
const BKP = path.join(__dirname, 'backups');
fs.mkdirSync(DATA, { recursive: true });
fs.mkdirSync(SRV, { recursive: true });
fs.mkdirSync(BKP, { recursive: true });
const DBF = path.join(DATA, 'db.json');
let db = { users: {}, sessions: {}, servers: {} };
if (fs.existsSync(DBF)) db = JSON.parse(fs.readFileSync(DBF, 'utf8'));
const save = () => fs.writeFileSync(DBF, JSON.stringify(db, null, 2));

/* ---------- runtime state (not persisted) ---------- */
const runtime = {};
const rt = id => (runtime[id] ||= { proc: null, status: 'offline', log: [], players: [] });
function addLog(r, line) { r.log.push(line); if (r.log.length > 500) r.log.shift(); }
function send(r, cmd) { if (r.proc && r.proc.stdin.writable) r.proc.stdin.write(cmd.replace(/[\r\n]/g, ' ') + '\n'); }
const validName = x => /^[A-Za-z0-9_]{1,16}$/.test(x || '');
const same = n => x => x.toLowerCase() === n.toLowerCase();
const validEmail = e => e.length <= 254 && /^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(e);

/* ---------- auth helpers ---------- */
function hashPw(pw, salt = crypto.randomBytes(16).toString('hex')) {
  return salt + ':' + crypto.scryptSync(pw, salt, 64).toString('hex');
}
function checkPw(pw, stored) {
  const [salt, h] = stored.split(':');
  const t = hashPw(pw, salt).split(':')[1];
  return crypto.timingSafeEqual(Buffer.from(h, 'hex'), Buffer.from(t, 'hex'));
}
function session(key) {
  const t = crypto.randomBytes(24).toString('hex');
  db.sessions[t] = key; save();
  return { token: t, name: db.users[key].name };
}
function auth(req, res, next) {
  const t = (req.headers.authorization || '').replace('Bearer ', '');
  const u = db.sessions[t];
  if (!u) return res.status(401).json({ error: 'Not signed in' });
  req.user = u; next();
}
/* ownerOnly = true -> subusers are not allowed */
function owned(req, res, ownerOnly) {
  const s = db.servers[req.params.id];
  const ok = s && (s.owner === req.user || (!ownerOnly && (s.subs || []).includes(req.user)));
  if (!ok) { res.status(404).json({ error: 'Server not found' }); return null; }
  return s;
}

/* ---------- custom address (name.domain) ---------- */
function slugify(n) {
  return String(n || '').toLowerCase().trim().replace(/[\s_]+/g, '-').replace(/[^a-z0-9-]/g, '').replace(/-+/g, '-').replace(/^-|-$/g, '').slice(0, 32);
}
function subError(sub) {
  if (sub.length < 3) return 'Name must be at least 3 letters or numbers';
  if (RESERVED.includes(sub)) return 'That name is reserved';
  if (Object.values(db.servers).some(x => x.sub === sub)) return 'That name is already used';
  return null;
}
async function cf(method, urlPath, body) {
  const resp = await fetch('https://api.cloudflare.com/client/v4/zones/' + CF_ZONE + urlPath, {
    method,
    headers: { Authorization: 'Bearer ' + CF_TOKEN, 'Content-Type': 'application/json' },
    body: body ? JSON.stringify(body) : undefined
  });
  const j = await resp.json();
  if (!j.success) throw new Error(JSON.stringify(j.errors));
  return j.result;
}
async function createSrv(s) {
  if (!CF_TOKEN || !CF_ZONE) return;
  const rec = await cf('POST', '/dns_records', {
    type: 'SRV', name: '_minecraft._tcp.' + s.sub + '.' + DOMAIN, ttl: 120,
    data: { service: '_minecraft', proto: '_tcp', name: s.sub + '.' + DOMAIN, priority: 0, weight: 5, port: s.port, target: SRV_TARGET }
  });
  s.srvId = rec.id; save();
}
async function deleteSrv(s) {
  if (!CF_TOKEN || !CF_ZONE || !s.srvId) return;
  await cf('DELETE', '/dns_records/' + s.srvId);
}

function view(s, u) {
  const r = rt(s.id);
  return { id: s.id, name: s.name, soft: s.soft, ver: s.ver, port: s.port, bport: s.bport, sub: s.sub, domain: DOMAIN, opts: s.opts,
           ops: s.ops, wl: s.wl, isOwner: s.owner === u,
           owner: db.users[s.owner] ? db.users[s.owner].name : s.owner,
           subs: (s.subs || []).map(k => db.users[k] ? db.users[k].name : k),
           status: r.status, players: r.players, log: r.log.slice(-300) };
}

/* ---------- software + version lists (fetched live, cached 1 hour) ---------- */
async function getJson(url) {
  const r = await fetch(url, { headers: UA, signal: AbortSignal.timeout(8000) });
  if (!r.ok) throw new Error('HTTP ' + r.status);
  return r.json();
}
const vparts = v => v.split('.').map(n => parseInt(n, 10) || 0);
function vcmp(a, b) { /* sorts newest first */
  const x = vparts(a), y = vparts(b);
  for (let i = 0; i < Math.max(x.length, y.length); i++) {
    const d = (y[i] || 0) - (x[i] || 0);
    if (d) return d;
  }
  return 0;
}
const okVer = v => /^\d+\.\d+(\.\d+)?$/.test(v) && vcmp(v, MIN_VER) <= 0;

async function loadSoftware() {
  const tasks = {
    Paper: async () => {
      try {
        const v = (await getJson('https://fill.papermc.io/v3/projects/paper')).versions;
        return Array.isArray(v) ? v : Object.values(v || {}).flat();
      } catch (e) {
        return (await getJson('https://api.papermc.io/v2/projects/paper')).versions;
      }
    },
    Purpur: async () => (await getJson('https://api.purpurmc.org/v2/purpur')).versions,
    Fabric: async () => (await getJson('https://meta.fabricmc.net/v2/versions/game')).filter(g => g.stable).map(g => g.version),
    Vanilla: async () => (await getJson('https://piston-meta.mojang.com/mc/game/version_manifest_v2.json')).versions.filter(v => v.type === 'release').map(v => v.id)
  };
  const got = {};
  await Promise.all(Object.entries(tasks).map(async ([name, fn]) => {
    try {
      const list = [...new Set((await fn()).filter(okVer))].sort(vcmp).slice(0, 40);
      if (list.length) got[name] = list;
    } catch (e) { console.log('Version list failed for ' + name + ':', e.message); }
  }));
  const out = {};
  SOFT_ORDER.forEach(n => { out[n] = got[n] || FALLBACK_VERS; });
  return out;
}
let SWC = null, SWT = 0;
async function getSoftware() {
  if (SWC && Date.now() - SWT < 3600000) return SWC;
  SWC = await loadSoftware(); SWT = Date.now();
  return SWC;
}
async function validSoft(soft, ver) {
  const sw = await getSoftware();
  return !!(sw[soft] && sw[soft].includes(ver));
}
getSoftware();

/* ---------- minecraft process management ---------- */
async function paperUrl(ver) {
  try {
    const j = await (await fetch(`https://fill.papermc.io/v3/projects/paper/versions/${ver}/builds/latest`, { headers: UA })).json();
    const u = j.downloads['server:default'].url;
    if (u) return u;
  } catch (e) { /* fall back to v2 */ }
  const b = await (await fetch(`https://api.papermc.io/v2/projects/paper/versions/${ver}/builds`, { headers: UA })).json();
  const l = b.builds[b.builds.length - 1];
  return `https://api.papermc.io/v2/projects/paper/versions/${ver}/builds/${l.build}/downloads/${l.downloads.application.name}`;
}
async function vanillaUrl(ver) {
  const m = await (await fetch('https://piston-meta.mojang.com/mc/game/version_manifest_v2.json')).json();
  const v = m.versions.find(x => x.id === ver);
  if (!v) throw new Error('Version not found');
  return (await (await fetch(v.url)).json()).downloads.server.url;
}
async function purpurUrl(ver) {
  return `https://api.purpurmc.org/v2/purpur/${ver}/latest/download`;
}
async function fabricUrl(ver) {
  const loaders = await getJson(`https://meta.fabricmc.net/v2/versions/loader/${ver}`);
  if (!Array.isArray(loaders) || !loaders.length) throw new Error('Fabric does not support ' + ver);
  const l = loaders.find(x => x.loader.stable) || loaders[0];
  const installers = await getJson('https://meta.fabricmc.net/v2/versions/installer');
  const i = installers.find(x => x.stable) || installers[0];
  return `https://meta.fabricmc.net/v2/versions/loader/${ver}/${l.loader.version}/${i.version}/server/jar`;
}
async function jarUrl(soft, ver) {
  if (soft === 'Paper') return paperUrl(ver);
  if (soft === 'Purpur') return purpurUrl(ver);
  if (soft === 'Fabric') return fabricUrl(ver);
  return vanillaUrl(ver);
}
async function ensureJar(s, r) {
  const dir = path.join(SRV, s.id), jar = path.join(dir, 'server.jar');
  if (fs.existsSync(jar) && s.jarKey === s.soft + s.ver) return;
  addLog(r, `[Nucleon] Downloading ${s.soft} ${s.ver}…`);
  const url = await jarUrl(s.soft, s.ver);
  const resp = await fetch(url, { headers: UA });
  if (!resp.ok) throw new Error('Download failed (HTTP ' + resp.status + ')');
  await pipeline(Readable.fromWeb(resp.body), fs.createWriteStream(jar));
  s.jarKey = s.soft + s.ver; save();
  addLog(r, '[Nucleon] Download complete.');
}
function writeProps(s, dir) {
  const o = s.opts;
  const p = {
    'server-port': s.port, motd: o.motd.replace(/[\r\n]/g, ' '), gamemode: o.gamemode,
    difficulty: o.difficulty, pvp: o.pvp, 'white-list': o.whitelist,
    'enforce-whitelist': o.whitelist, 'online-mode': o.onlineMode, 'max-players': o.maxPlayers
  };
  fs.writeFileSync(path.join(dir, 'server.properties'),
    Object.entries(p).map(([k, v]) => `${k}=${v}`).join('\n') + '\n');
}

/* ---------- crossplay (Geyser + Floodgate) ---------- */
const GEYSER_BASE = 'https://download.geysermc.org/v2/projects';
async function grab(url, dest) {
  const resp = await fetch(url, { headers: UA });
  if (!resp.ok) throw new Error('Download failed (HTTP ' + resp.status + ') ' + url);
  await pipeline(Readable.fromWeb(resp.body), fs.createWriteStream(dest));
}
function assignBport(s) {
  if (s.bport) return;
  const used = new Set(Object.values(db.servers).map(x => x.bport).filter(Boolean));
  let p = BASE_BEDROCK_PORT; while (used.has(p)) p++;
  s.bport = p; save();
}
async function ensureCrossplay(s, r, dir) {
  assignBport(s);
  const pl = path.join(dir, 'plugins');
  fs.mkdirSync(pl, { recursive: true });
  const g = path.join(pl, 'Geyser-Spigot.jar'), f = path.join(pl, 'floodgate-spigot.jar');
  if (!fs.existsSync(g)) {
    addLog(r, '[Nucleon] Downloading Geyser…');
    await grab(`${GEYSER_BASE}/geyser/versions/latest/builds/latest/downloads/spigot`, g);
  }
  if (!fs.existsSync(f)) {
    addLog(r, '[Nucleon] Downloading Floodgate…');
    await grab(`${GEYSER_BASE}/floodgate/versions/latest/builds/latest/downloads/spigot`, f);
  }
  const cdir = path.join(pl, 'Geyser-Spigot');
  fs.mkdirSync(cdir, { recursive: true });
  const cfg = path.join(cdir, 'config.yml');
  if (!fs.existsSync(cfg)) {
    fs.writeFileSync(cfg,
`bedrock:
  address: 0.0.0.0
  port: ${s.bport}
remote:
  address: auto
  port: auto
  auth-type: floodgate
`);
  }
  addLog(r, `[Nucleon] Crossplay on. Bedrock port: ${s.bport} (UDP)`);
}
function removeCrossplay(dir) {
  const pl = path.join(dir, 'plugins');
  fs.rmSync(path.join(pl, 'Geyser-Spigot.jar'), { force: true });
  fs.rmSync(path.join(pl, 'floodgate-spigot.jar'), { force: true });
}

function handleLine(s, r, line) {
  addLog(r, line);
  if (/UnsupportedClassVersionError/.test(line)) {
    addLog(r, '[Nucleon] This version needs a newer Java than the one installed. Install the Java version it asks for, then start again.');
  }
  if (/Done \(.*\)! For help/.test(line)) {
    r.status = 'online';
    s.wl.forEach(n => send(r, 'whitelist add ' + n));
    s.ops.forEach(n => send(r, 'op ' + n));
    /* run changes made while the server was offline (bans, unbans, IP bans) */
    (s.queue || []).forEach(c => send(r, c));
    s.queue = []; save();
  }
  let m = line.match(/: (\S+) joined the game/);
  if (m && !r.players.includes(m[1])) r.players.push(m[1]);
  if (m) {
    s.known ||= [];
    if (!s.known.some(same(m[1]))) { s.known.push(m[1]); if (s.known.length > 500) s.known.shift(); save(); }
  }
  m = line.match(/: (\S+) left the game/);
  if (m) r.players = r.players.filter(p => p !== m[1]);
}
async function startServer(s) {
  const r = rt(s.id);
  if (r.status !== 'offline') return;
  r.status = 'starting'; r.players = [];
  addLog(r, '[Nucleon] Preparing server…');
  try {
    const dir = path.join(SRV, s.id);
    fs.mkdirSync(dir, { recursive: true });
    await ensureJar(s, r);
    if (s.opts.crossplay && PLUGIN_SOFT.includes(s.soft)) await ensureCrossplay(s, r, dir);
    else removeCrossplay(dir);
    fs.writeFileSync(path.join(dir, 'eula.txt'), 'eula=true\n');
    writeProps(s, dir);
    const proc = spawn('java', [`-Xmx${RAM}`, '-Xms256M', '-jar', 'server.jar', 'nogui'], { cwd: dir });
    r.proc = proc;
    const onData = d => String(d).split(/\r?\n/).filter(Boolean).forEach(l => handleLine(s, r, l));
    proc.stdout.on('data', onData);
    proc.stderr.on('data', onData);
    proc.on('error', e => {
      addLog(r, '[Nucleon] Could not start Java: ' + e.message + ' (is Java 21 installed?)');
      r.status = 'offline'; r.proc = null;
    });
    proc.on('exit', code => {
      addLog(r, `[Nucleon] Server stopped (exit code ${code}).`);
      r.status = 'offline'; r.proc = null; r.players = [];
    });
  } catch (e) {
    addLog(r, '[Nucleon] Start failed: ' + e.message);
    r.status = 'offline';
  }
}
function stopServer(s) {
  const r = rt(s.id);
  if (!r.proc) return;
  r.status = 'stopping';
  send(r, 'stop');
  const p = r.proc;
  setTimeout(() => { if (r.proc === p) p.kill(); }, 30000);
}

/* ---------- files / backups helpers ---------- */
const sdir = s => path.join(SRV, s.id);
const bdir = s => path.join(BKP, s.id);
function safe(s, rel) {
  const base = sdir(s);
  const p = path.resolve(base, '.' + path.sep + String(rel || ''));
  if (p !== base && !p.startsWith(base + path.sep)) return null;
  return p;
}
const bakOk = n => /^[\w.-]+\.tar\.gz$/.test(n);
const jarOk = n => /^[\w.\- +()\[\]]+\.jar$/.test(n);
function listBackups(s) {
  const d = bdir(s);
  if (!fs.existsSync(d)) return [];
  return fs.readdirSync(d).filter(bakOk).map(f => {
    const st = fs.statSync(path.join(d, f));
    return { name: f, size: st.size, time: st.mtimeMs };
  }).sort((a, b) => b.time - a.time);
}
function runTar(args) {
  return new Promise((ok, bad) => {
    const p = spawn('tar', args);
    let err = '';
    p.stderr.on('data', d => err += d);
    p.on('error', bad);
    p.on('exit', c => c === 0 ? ok() : bad(new Error(err.trim() || 'tar failed')));
  });
}
/* what kind of add-ons this software takes (Modrinth type, loader, folder) */
function kindOf(s) {
  if (s.soft === 'Fabric') return { type: 'mod', loader: 'fabric', dir: 'mods' };
  if (PLUGIN_SOFT.includes(s.soft)) return { type: 'plugin', loader: 'paper', dir: 'plugins' };
  return null;
}

/* ---------- web app + API ---------- */
const app = express();
app.use(express.json({ limit: '1mb' }));
app.use(express.static(path.join(__dirname, 'public')));

app.get('/api/config', (q, r) => r.json({ host: process.env.PUBLIC_HOST || null, domain: DOMAIN }));
app.get('/api/software', async (q, r) => r.json({ software: await getSoftware() }));

app.get('/api/check-name', auth, (req, res) => {
  const sub = slugify(req.query.name);
  const err = subError(sub);
  res.json({ sub, address: sub + '.' + DOMAIN, ok: !err, error: err });
});

app.post('/api/register', (req, res) => {
  const { name = '', email = '', password = '' } = req.body || {};
  const mail = String(email).trim().toLowerCase();
  const pw = String(password);
  if (!/^[A-Za-z0-9_]{3,16}$/.test(name)) return res.status(400).json({ error: 'Username must be 3-16 letters, numbers or _' });
  if (!validEmail(mail)) return res.status(400).json({ error: 'Enter a valid email address' });
  if (pw.length < 6) return res.status(400).json({ error: 'Password must be at least 6 characters' });
  const key = name.toLowerCase();
  if (db.users[key]) return res.status(400).json({ error: 'Username already taken' });
  if (Object.values(db.users).some(u => u.email === mail)) return res.status(400).json({ error: 'Email already in use' });
  db.users[key] = { name, email: mail, pw: hashPw(pw) };
  res.json(session(key));
});
app.post('/api/login', (req, res) => {
  const { name = '', password = '' } = req.body || {};
  const id = String(name).trim().toLowerCase();
  const key = db.users[id] ? id : Object.keys(db.users).find(k => db.users[k].email === id);
  const u = key && db.users[key];
  if (!u || !checkPw(String(password), u.pw)) return res.status(400).json({ error: 'Wrong email/username or password' });
  res.json(session(key));
});

app.get('/api/servers', auth, (req, res) =>
  res.json(Object.values(db.servers)
    .filter(s => s.owner === req.user || (s.subs || []).includes(req.user))
    .map(s => { const v = view(s, req.user); delete v.log; return v; })));

app.post('/api/servers', auth, async (req, res) => {
  const b = req.body || {};
  const mine = Object.values(db.servers).filter(s => s.owner === req.user);
  if (mine.length >= MAX_SERVERS_PER_USER) return res.status(400).json({ error: `Limit of ${MAX_SERVERS_PER_USER} servers per account` });
  if (!b.eula) return res.status(400).json({ error: 'You must accept the Minecraft EULA' });
  if (!(await validSoft(b.soft, b.ver))) return res.status(400).json({ error: 'Invalid software or version' });
  const sub = slugify(b.name);
  const subErr = subError(sub);
  if (subErr) return res.status(400).json({ error: subErr });
  const used = new Set(Object.values(db.servers).map(s => s.port));
  let port = BASE_MC_PORT; while (used.has(port)) port++;
  const id = crypto.randomBytes(6).toString('hex');
  db.servers[id] = {
    id, owner: req.user, name: String(b.name || 'My Server').slice(0, 32), soft: b.soft, ver: b.ver, port, sub,
    opts: { motd: 'A Nucleon server', gamemode: 'survival', difficulty: 'normal', pvp: true, whitelist: false, onlineMode: true, maxPlayers: 10 },
    ops: [], wl: [], subs: []
  };
  save();
  createSrv(db.servers[id]).catch(e => console.log('DNS error:', e.message));
  res.json(view(db.servers[id], req.user));
});

app.get('/api/servers/:id', auth, (req, res) => { const s = owned(req, res); if (s) res.json(view(s, req.user)); });

app.post('/api/servers/:id/start', auth, (req, res) => { const s = owned(req, res); if (!s) return; startServer(s); res.json({ ok: true }); });
app.post('/api/servers/:id/stop', auth, (req, res) => { const s = owned(req, res); if (!s) return; stopServer(s); res.json({ ok: true }); });
app.post('/api/servers/:id/restart', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const r = rt(s.id);
  if (r.proc) { r.proc.once('exit', () => setTimeout(() => startServer(s), 1000)); stopServer(s); }
  else startServer(s);
  res.json({ ok: true });
});

app.post('/api/servers/:id/command', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const r = rt(s.id);
  const cmd = String((req.body || {}).cmd || '').replace(/[\r\n]/g, ' ').trim().slice(0, 200);
  if (!cmd) return res.status(400).json({ error: 'Empty command' });
  const [a, b, c] = cmd.replace(/^\//, '').split(/\s+/);
  if (a === 'op' && validName(b) && !s.ops.includes(b)) s.ops.push(b);
  if (a === 'deop' && validName(b)) s.ops = s.ops.filter(x => x !== b);
  if (a === 'whitelist' && b === 'add' && validName(c) && !s.wl.includes(c)) s.wl.push(c);
  if (a === 'whitelist' && b === 'remove' && validName(c)) s.wl = s.wl.filter(x => x !== c);
  save();
  if (r.status !== 'online') {
    if (['op', 'deop', 'whitelist'].includes(a)) return res.json({ ok: true, note: 'Saved. Applies when the server starts.' });
    return res.status(400).json({ error: 'Server must be online to run commands' });
  }
  addLog(r, '> ' + cmd); send(r, cmd); res.json({ ok: true });
});

app.put('/api/servers/:id/options', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const o = req.body || {};
  if (!['survival', 'creative', 'adventure', 'spectator'].includes(o.gamemode)) return res.status(400).json({ error: 'Bad gamemode' });
  if (!['peaceful', 'easy', 'normal', 'hard'].includes(o.difficulty)) return res.status(400).json({ error: 'Bad difficulty' });
  const mp = parseInt(o.maxPlayers, 10);
  if (!(mp >= 1 && mp <= 20)) return res.status(400).json({ error: 'Max players must be 1-20' });
  if (o.crossplay && !PLUGIN_SOFT.includes(s.soft)) return res.status(400).json({ error: 'Crossplay needs Paper or Purpur software' });
  s.opts = { motd: String(o.motd || '').slice(0, 80), gamemode: o.gamemode, difficulty: o.difficulty,
             pvp: !!o.pvp, whitelist: !!o.whitelist, onlineMode: !!o.onlineMode, maxPlayers: mp,
             crossplay: !!o.crossplay };
  if (s.opts.crossplay) assignBport(s);
  save(); res.json({ ok: true });
});

app.patch('/api/servers/:id', auth, async (req, res) => {
  const s = owned(req, res, true); if (!s) return;
  const b = req.body || {};
  if (b.name) s.name = String(b.name).slice(0, 32);
  if (b.soft || b.ver) {
    if (rt(s.id).status !== 'offline') return res.status(400).json({ error: 'Stop the server first' });
    const ns = b.soft || s.soft, nv = b.ver || s.ver;
    if (!(await validSoft(ns, nv))) return res.status(400).json({ error: nv + ' is not available for ' + ns });
    s.soft = ns; s.ver = nv;
  }
  save(); res.json(view(s, req.user));
});

app.delete('/api/servers/:id', auth, (req, res) => {
  const s = owned(req, res, true); if (!s) return;
  if (rt(s.id).status !== 'offline') return res.status(400).json({ error: 'Stop the server first' });
  fs.rmSync(sdir(s), { recursive: true, force: true });
  fs.rmSync(bdir(s), { recursive: true, force: true });
  deleteSrv(s).catch(e => console.log('DNS error:', e.message));
  delete db.servers[s.id]; delete runtime[s.id]; save();
  res.json({ ok: true });
});

/* ----- files ----- */
app.get('/api/servers/:id/files', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const p = safe(s, req.query.path);
  if (!p) return res.status(400).json({ error: 'Bad path' });
  try {
    if (!fs.existsSync(p) || !fs.statSync(p).isDirectory()) return res.json({ items: [] });
    const items = fs.readdirSync(p, { withFileTypes: true }).map(d => {
      let size = 0;
      try { if (!d.isDirectory()) size = fs.statSync(path.join(p, d.name)).size; } catch (e) { /* ignore */ }
      return { name: d.name, dir: d.isDirectory(), size };
    });
    items.sort((a, b) => (b.dir - a.dir) || a.name.localeCompare(b.name));
    res.json({ items });
  } catch (e) { res.status(500).json({ error: 'Could not read folder' }); }
});
app.get('/api/servers/:id/file', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const p = safe(s, req.query.path);
  if (!p) return res.status(400).json({ error: 'Bad path' });
  try {
    const st = fs.statSync(p);
    if (!st.isFile()) return res.status(400).json({ error: 'Not a file' });
    if (st.size > 512 * 1024) return res.status(400).json({ error: 'File too large to edit here (max 512 KB)' });
    const buf = fs.readFileSync(p);
    if (buf.includes(0)) return res.status(400).json({ error: 'Binary files cannot be edited' });
    res.json({ content: buf.toString('utf8') });
  } catch (e) { res.status(404).json({ error: 'File not found' }); }
});
app.put('/api/servers/:id/file', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const b = req.body || {};
  const p = safe(s, b.path);
  if (!p || p === sdir(s)) return res.status(400).json({ error: 'Bad path' });
  if (typeof b.content !== 'string' || b.content.length > 512 * 1024) return res.status(400).json({ error: 'Content too large (max 512 KB)' });
  if (!fs.existsSync(path.dirname(p))) return res.status(400).json({ error: 'Folder does not exist' });
  fs.writeFileSync(p, b.content);
  res.json({ ok: true });
});
app.delete('/api/servers/:id/file', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const p = safe(s, req.query.path);
  if (!p || p === sdir(s)) return res.status(400).json({ error: 'Bad path' });
  fs.rmSync(p, { recursive: true, force: true });
  res.json({ ok: true });
});

/* ----- backups ----- */
app.get('/api/servers/:id/backups', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  res.json({ items: listBackups(s), max: MAX_BACKUPS });
});
app.post('/api/servers/:id/backups', auth, async (req, res) => {
  const s = owned(req, res); if (!s) return;
  if (!fs.existsSync(sdir(s))) return res.status(400).json({ error: 'Start the server once before backing it up' });
  const r = rt(s.id);
  try {
    if (r.status === 'online') { send(r, 'save-all flush'); await new Promise(x => setTimeout(x, 3000)); }
    fs.mkdirSync(bdir(s), { recursive: true });
    const name = 'backup-' + new Date().toISOString().replace(/[:.]/g, '-') + '.tar.gz';
    await runTar(['-czf', path.join(bdir(s), name), '-C', SRV, s.id]);
    listBackups(s).slice(MAX_BACKUPS).forEach(b => fs.rmSync(path.join(bdir(s), b.name), { force: true }));
    res.json({ ok: true, name });
  } catch (e) { res.status(500).json({ error: 'Backup failed: ' + e.message }); }
});
app.post('/api/servers/:id/backups/:name/restore', auth, async (req, res) => {
  const s = owned(req, res, true); if (!s) return;
  if (!bakOk(req.params.name)) return res.status(400).json({ error: 'Bad backup name' });
  const file = path.join(bdir(s), req.params.name);
  if (!fs.existsSync(file)) return res.status(404).json({ error: 'Backup not found' });
  if (rt(s.id).status !== 'offline') return res.status(400).json({ error: 'Stop the server first' });
  const dir = sdir(s), old = dir + '.old';
  try {
    fs.rmSync(old, { recursive: true, force: true });
    if (fs.existsSync(dir)) fs.renameSync(dir, old);
    await runTar(['-xzf', file, '-C', SRV]);
    fs.rmSync(old, { recursive: true, force: true });
    res.json({ ok: true });
  } catch (e) {
    fs.rmSync(dir, { recursive: true, force: true });
    if (fs.existsSync(old)) fs.renameSync(old, dir);
    res.status(500).json({ error: 'Restore failed: ' + e.message });
  }
});
app.delete('/api/servers/:id/backups/:name', auth, (req, res) => {
  const s = owned(req, res, true); if (!s) return;
  if (!bakOk(req.params.name)) return res.status(400).json({ error: 'Bad backup name' });
  fs.rmSync(path.join(bdir(s), req.params.name), { force: true });
  res.json({ ok: true });
});

/* ----- plugins (Paper/Purpur) and mods (Fabric), via Modrinth ----- */
app.get('/api/servers/:id/plugins', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const K = kindOf(s);
  if (!K) return res.json({ items: [] });
  const d = path.join(sdir(s), K.dir);
  const items = fs.existsSync(d)
    ? fs.readdirSync(d).filter(jarOk).map(f => ({ name: f, size: fs.statSync(path.join(d, f)).size })) : [];
  res.json({ items });
});
app.get('/api/servers/:id/plugins/search', auth, async (req, res) => {
  const s = owned(req, res); if (!s) return;
  const K = kindOf(s);
  if (!K) return res.status(400).json({ error: 'This software does not support plugins or mods' });
  try {
    const facets = JSON.stringify([['project_type:' + K.type], ['categories:' + K.loader], ['versions:' + s.ver]]);
    const url = 'https://api.modrinth.com/v2/search?limit=12&query=' + encodeURIComponent(String(req.query.q || '').slice(0, 60)) +
      '&facets=' + encodeURIComponent(facets);
    const j = await (await fetch(url, { headers: UA })).json();
    res.json({ hits: (j.hits || []).map(h => ({ id: h.project_id, title: h.title, desc: h.description, icon: h.icon_url, downloads: h.downloads })) });
  } catch (e) { res.status(500).json({ error: 'Search failed' }); }
});
app.post('/api/servers/:id/plugins/install', auth, async (req, res) => {
  const s = owned(req, res); if (!s) return;
  const K = kindOf(s);
  if (!K) return res.status(400).json({ error: 'This software does not support plugins or mods' });
  const id = String((req.body || {}).id || '');
  if (!/^[A-Za-z0-9]{6,12}$/.test(id)) return res.status(400).json({ error: 'Bad project id' });
  try {
    const url = `https://api.modrinth.com/v2/project/${id}/version?loaders=${encodeURIComponent(JSON.stringify([K.loader]))}&game_versions=${encodeURIComponent(JSON.stringify([s.ver]))}`;
    const vs = await (await fetch(url, { headers: UA })).json();
    if (!Array.isArray(vs) || !vs.length) return res.status(400).json({ error: 'No compatible version for ' + s.ver });
    const f = vs[0].files.find(x => x.primary) || vs[0].files[0];
    const name = path.basename(String(f.filename));
    if (!jarOk(name)) return res.status(400).json({ error: 'Unsupported file' });
    if (new URL(f.url).hostname !== 'cdn.modrinth.com') return res.status(400).json({ error: 'Untrusted download source' });
    const dir = path.join(sdir(s), K.dir);
    fs.mkdirSync(dir, { recursive: true });
    await grab(f.url, path.join(dir, name));
    res.json({ ok: true, name });
  } catch (e) { res.status(500).json({ error: 'Install failed: ' + e.message }); }
});
app.delete('/api/servers/:id/plugins/:file', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const K = kindOf(s);
  if (!K) return res.status(400).json({ error: 'Nothing to remove' });
  if (!jarOk(req.params.file)) return res.status(400).json({ error: 'Bad file name' });
  fs.rmSync(path.join(sdir(s), K.dir, req.params.file), { force: true });
  res.json({ ok: true });
});

/* ----- players: whitelist, operators, bans, banned IPs ----- */
function playerList(s) {
  s.known ||= []; s.bans ||= [];
  const names = new Map();
  [...s.known, ...s.wl, ...s.ops, ...s.bans.map(b => b.name)].forEach(n => { if (!names.has(n.toLowerCase())) names.set(n.toLowerCase(), n); });
  const online = rt(s.id).players;
  return [...names.values()].map(n => {
    const ban = s.bans.find(b => same(n)(b.name));
    return { name: n, wl: s.wl.some(same(n)), op: s.ops.some(same(n)), ban: !!ban, reason: ban ? ban.reason : '', online: online.includes(n) };
  });
}
/* updates the saved lists and returns the console command that matches */
function applyList(s, kind, name, on, reason) {
  s.bans ||= [];
  if (kind === 'wl') { s.wl = s.wl.filter(x => !same(name)(x)); if (on) s.wl.push(name); return (on ? 'whitelist add ' : 'whitelist remove ') + name; }
  if (kind === 'op') { s.ops = s.ops.filter(x => !same(name)(x)); if (on) s.ops.push(name); return (on ? 'op ' : 'deop ') + name; }
  s.bans = s.bans.filter(b => !same(name)(b.name)); if (on) s.bans.push({ name, reason });
  return on ? 'ban ' + name + (reason ? ' ' + reason : '') : 'pardon ' + name;
}
function runOrQueue(s, cmd) {
  const r = rt(s.id);
  if (r.status === 'online') return send(r, cmd);
  s.queue ||= []; s.queue.push(cmd);
  if (s.queue.length > 200) s.queue.shift();
}
const cleanReason = x => String(x || '').replace(/[\r\n]/g, ' ').trim().slice(0, 100);

app.get('/api/servers/:id/players', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  s.bannedIps ||= [];
  res.json({ players: playerList(s), bannedIps: s.bannedIps, status: rt(s.id).status });
});
function changePlayers(req, res, on) {
  const s = owned(req, res); if (!s) return;
  const kind = req.params.kind;
  if (!['wl', 'op', 'ban'].includes(kind)) return res.status(400).json({ error: 'Unknown list' });
  const b = req.body || {};
  const names = on ? (Array.isArray(b.names) ? b.names : []) : [req.params.name];
  const clean = [...new Set(names.map(x => String(x).trim()).filter(Boolean))].slice(0, 50);
  if (!clean.length) return res.status(400).json({ error: 'Enter a username' });
  const bad = clean.find(n => !validName(n));
  if (bad) return res.status(400).json({ error: bad.slice(0, 20) + ' is not a valid username' });
  const reason = cleanReason(b.reason);
  clean.forEach(n => runOrQueue(s, applyList(s, kind, n, on, reason)));
  save();
  res.json({ ok: true, note: rt(s.id).status === 'online' ? undefined : 'Saved. Applies when the server starts.' });
}
app.post('/api/servers/:id/players/:kind', auth, (req, res) => changePlayers(req, res, true));
app.delete('/api/servers/:id/players/:kind/:name', auth, (req, res) => changePlayers(req, res, false));

app.post('/api/servers/:id/banned-ips', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const b = req.body || {};
  const ipsIn = [...new Set((Array.isArray(b.ips) ? b.ips : []).map(x => String(x).trim()).filter(Boolean))].slice(0, 50);
  if (!ipsIn.length) return res.status(400).json({ error: 'Enter an IP address' });
  const bad = ipsIn.find(i => !net.isIP(i));
  if (bad) return res.status(400).json({ error: bad.slice(0, 45) + ' is not a valid IP address' });
  const reason = cleanReason(b.reason);
  s.bannedIps ||= [];
  ipsIn.forEach(ip => {
    s.bannedIps = s.bannedIps.filter(x => x.ip !== ip); s.bannedIps.push({ ip, reason });
    runOrQueue(s, 'ban-ip ' + ip + (reason ? ' ' + reason : ''));
  });
  save(); res.json({ ok: true });
});
app.delete('/api/servers/:id/banned-ips/:ip', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const ip = String(req.params.ip);
  if (!net.isIP(ip)) return res.status(400).json({ error: 'Not a valid IP address' });
  s.bannedIps = (s.bannedIps || []).filter(x => x.ip !== ip);
  runOrQueue(s, 'pardon-ip ' + ip);
  save(); res.json({ ok: true });
});

/* ----- subusers ----- */
app.post('/api/servers/:id/subusers', auth, (req, res) => {
  const s = owned(req, res, true); if (!s) return;
  const key = String((req.body || {}).name || '').trim().toLowerCase();
  s.subs ||= [];
  if (!db.users[key]) return res.status(400).json({ error: 'No Nucleon account with that username' });
  if (key === s.owner) return res.status(400).json({ error: 'That is you' });
  if (s.subs.includes(key)) return res.status(400).json({ error: 'Already added' });
  if (s.subs.length >= MAX_SUBUSERS) return res.status(400).json({ error: `Limit of ${MAX_SUBUSERS} subusers` });
  s.subs.push(key); save();
  res.json({ ok: true });
});
app.delete('/api/servers/:id/subusers/:name', auth, (req, res) => {
  const s = owned(req, res, true); if (!s) return;
  const key = String(req.params.name).toLowerCase();
  s.subs = (s.subs || []).filter(x => x !== key); save();
  res.json({ ok: true });
});

app.listen(WEB_PORT, '0.0.0.0', () => console.log(`Nucleon running on port ${WEB_PORT}`));

/* stop all servers cleanly on Ctrl+C */
process.on('SIGINT', () => {
  Object.values(db.servers).forEach(s => stopServer(s));
  setTimeout(() => process.exit(0), 4000);
});