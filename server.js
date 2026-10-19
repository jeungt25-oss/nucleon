const express = require('express');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { spawn } = require('child_process');
const { pipeline } = require('stream/promises');
const { Readable } = require('stream');

/* ---------- config ---------- */
const WEB_PORT = process.env.PORT || 3000;
const BASE_MC_PORT = 25565;
const BASE_BEDROCK_PORT = 19132;
const MAX_SERVERS_PER_USER = 3;
const RAM = '1G';
const VERS = ['1.21.4', '1.21.1', '1.20.6', '1.20.4', '1.19.4', '1.18.2'];
const SOFT = ['Paper', 'Vanilla'];
const UA = { 'User-Agent': 'Nucleon/1.0 (Creed Inc.)' };

/* custom address settings */
const DOMAIN = process.env.DOMAIN || 'creeds.inc';
const RESERVED = ['www', 'api', 'admin', 'mail', 'play', 'panel', 'dashboard', 'ftp', 'ns1', 'ns2', 'root', 'support'];
const CF_TOKEN = process.env.CF_TOKEN || '';
const CF_ZONE = process.env.CF_ZONE || '';
const SRV_TARGET = process.env.SRV_TARGET || 'play.' + DOMAIN;

const DATA = path.join(__dirname, 'data');
const SRV = path.join(__dirname, 'servers');
fs.mkdirSync(DATA, { recursive: true });
fs.mkdirSync(SRV, { recursive: true });
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
function owned(req, res) {
  const s = db.servers[req.params.id];
  if (!s || s.owner !== req.user) { res.status(404).json({ error: 'Server not found' }); return null; }
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

function view(s) {
  const r = rt(s.id);
  return { id: s.id, name: s.name, soft: s.soft, ver: s.ver, port: s.port, bport: s.bport, sub: s.sub, domain: DOMAIN, opts: s.opts,
           ops: s.ops, wl: s.wl, status: r.status, players: r.players, log: r.log.slice(-300) };
}

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
async function ensureJar(s, r) {
  const dir = path.join(SRV, s.id), jar = path.join(dir, 'server.jar');
  if (fs.existsSync(jar) && s.jarKey === s.soft + s.ver) return;
  addLog(r, `[Nucleon] Downloading ${s.soft} ${s.ver}…`);
  const url = s.soft === 'Paper' ? await paperUrl(s.ver) : await vanillaUrl(s.ver);
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
  if (/Done \(.*\)! For help/.test(line)) {
    r.status = 'online';
    s.wl.forEach(n => send(r, 'whitelist add ' + n));
    s.ops.forEach(n => send(r, 'op ' + n));
  }
  let m = line.match(/: (\S+) joined the game/);
  if (m && !r.players.includes(m[1])) r.players.push(m[1]);
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
    if (s.opts.crossplay && s.soft === 'Paper') await ensureCrossplay(s, r, dir);
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

/* ---------- web app + API ---------- */
const app = express();
app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

app.get('/api/config', (q, r) => r.json({ host: process.env.PUBLIC_HOST || null, domain: DOMAIN }));

app.get('/api/check-name', auth, (req, res) => {
  const sub = slugify(req.query.name);
  const err = subError(sub);
  res.json({ sub, address: sub + '.' + DOMAIN, ok: !err, error: err });
});

app.post('/api/register', (req, res) => {
  const { name = '', password = '' } = req.body || {};
  if (!/^[A-Za-z0-9_]{3,16}$/.test(name)) return res.status(400).json({ error: 'Username must be 3-16 letters, numbers or _' });
  if (password.length < 6) return res.status(400).json({ error: 'Password must be at least 6 characters' });
  const key = name.toLowerCase();
  if (db.users[key]) return res.status(400).json({ error: 'Username already taken' });
  db.users[key] = { name, pw: hashPw(password) };
  res.json(session(key));
});
app.post('/api/login', (req, res) => {
  const { name = '', password = '' } = req.body || {};
  const key = String(name).toLowerCase(), u = db.users[key];
  if (!u || !checkPw(String(password), u.pw)) return res.status(400).json({ error: 'Wrong username or password' });
  res.json(session(key));
});

app.get('/api/servers', auth, (req, res) =>
  res.json(Object.values(db.servers).filter(s => s.owner === req.user).map(s => {
    const v = view(s); delete v.log; return v;
  })));

app.post('/api/servers', auth, (req, res) => {
  const b = req.body || {};
  const mine = Object.values(db.servers).filter(s => s.owner === req.user);
  if (mine.length >= MAX_SERVERS_PER_USER) return res.status(400).json({ error: `Limit of ${MAX_SERVERS_PER_USER} servers per account` });
  if (!b.eula) return res.status(400).json({ error: 'You must accept the Minecraft EULA' });
  if (!SOFT.includes(b.soft) || !VERS.includes(b.ver)) return res.status(400).json({ error: 'Invalid software or version' });
  const sub = slugify(b.name);
  const subErr = subError(sub);
  if (subErr) return res.status(400).json({ error: subErr });
  const used = new Set(Object.values(db.servers).map(s => s.port));
  let port = BASE_MC_PORT; while (used.has(port)) port++;
  const id = crypto.randomBytes(6).toString('hex');
  db.servers[id] = {
    id, owner: req.user, name: String(b.name || 'My Server').slice(0, 32), soft: b.soft, ver: b.ver, port, sub,
    opts: { motd: 'A Nucleon server', gamemode: 'survival', difficulty: 'normal', pvp: true, whitelist: false, onlineMode: true, maxPlayers: 10 },
    ops: [], wl: []
  };
  save();
  createSrv(db.servers[id]).catch(e => console.log('DNS error:', e.message));
  res.json(view(db.servers[id]));
});

app.get('/api/servers/:id', auth, (req, res) => { const s = owned(req, res); if (s) res.json(view(s)); });

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
  if (o.crossplay && s.soft !== 'Paper') return res.status(400).json({ error: 'Crossplay needs Paper software' });
  s.opts = { motd: String(o.motd || '').slice(0, 80), gamemode: o.gamemode, difficulty: o.difficulty,
             pvp: !!o.pvp, whitelist: !!o.whitelist, onlineMode: !!o.onlineMode, maxPlayers: mp,
             crossplay: !!o.crossplay };
  if (s.opts.crossplay) assignBport(s);
  save(); res.json({ ok: true });
});

app.patch('/api/servers/:id', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  const b = req.body || {};
  if (b.name) s.name = String(b.name).slice(0, 32);
  if (b.soft || b.ver) {
    if (rt(s.id).status !== 'offline') return res.status(400).json({ error: 'Stop the server first' });
    if (b.soft && SOFT.includes(b.soft)) s.soft = b.soft;
    if (b.ver && VERS.includes(b.ver)) s.ver = b.ver;
  }
  save(); res.json(view(s));
});

app.delete('/api/servers/:id', auth, (req, res) => {
  const s = owned(req, res); if (!s) return;
  if (rt(s.id).status !== 'offline') return res.status(400).json({ error: 'Stop the server first' });
  fs.rmSync(path.join(SRV, s.id), { recursive: true, force: true });
  deleteSrv(s).catch(e => console.log('DNS error:', e.message));
  delete db.servers[s.id]; delete runtime[s.id]; save();
  res.json({ ok: true });
});

app.listen(WEB_PORT, '0.0.0.0', () => console.log(`Nucleon running on port ${WEB_PORT}`));

/* stop all servers cleanly on Ctrl+C */
process.on('SIGINT', () => {
  Object.values(db.servers).forEach(s => stopServer(s));
  setTimeout(() => process.exit(0), 4000);
});