const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
const { open, search, neighborhood, facts } = require('./lib/graphdb');
const { locate, localSource, modulePath } = require('./lib/leansource');
const { LeanStatements } = require('./lib/lean');

const GITHUB = 'https://github.com/leanprover-community/mathlib4/blob/master/';
const RAW = 'https://raw.githubusercontent.com/leanprover-community/mathlib4/master/';
const CACHE_FILES = 40;
const MAX_BODY = 256 * 1024;

// Downloads one Lean file from Mathlib's master branch; null when it is not there.
async function fetchFromGitHub(filePath) {
  const res = await fetch(RAW + filePath, { signal: AbortSignal.timeout(10_000) });
  if (res.status === 404) return null;
  if (!res.ok) throw new Error(`GitHub answered ${res.status}`);
  return res.text();
}

const PUBLIC = path.join(__dirname, 'public');
const STATIC = {
  '/': ['index.html', 'text/html; charset=utf-8'],
  '/index.html': ['index.html', 'text/html; charset=utf-8'],
  '/lean.js': ['lean.js', 'text/javascript; charset=utf-8'],
  '/lean-latex.js': ['lean-latex.js', 'text/javascript; charset=utf-8'],
  '/lean-phrases.js': ['lean-phrases.js', 'text/javascript; charset=utf-8'],
  '/lean-outline.js': ['lean-outline.js', 'text/javascript; charset=utf-8'],
};

// `lean`, when given, is a LeanStatements: the source of statements as Lean elaborates them.
function createServer(dbPath, { fetchSource = fetchFromGitHub, lean = null } = {}) {
  const db = open(dbPath);

  // Adds to each node row the elaborated statement already known for it, as `lean`.
  const withLean = (rows) => {
    if (!lean || !rows.length) return rows;
    const known = lean.cached(rows.map((r) => r.name), Object.fromEntries(rows.map((r) => [r.name, r.kind])));
    for (const row of rows) if (known[row.name]) row.lean = known[row.name];
    return rows;
  };
  const answer = (result) => {
    if (result) withLean([result.focus, ...result.out.nodes, ...result.in.nodes]);
    return result;
  };
  // Elaborated statements for `names`, asking Lean for the ones not yet known.
  const elaborate = async (names) => {
    if (!lean) return { state: 'off', statements: {} };
    const wanted = [...new Set(names.filter((n) => typeof n === 'string'))].slice(0, 400);
    const decls = wanted.length
      ? db.prepare(`SELECT name, kind FROM nodes WHERE name IN (${wanted.map(() => '?').join(',')})`).all(...wanted).map((r) => ({ ...r }))
      : [];
    const statements = await lean.statements(decls);
    return { state: lean.state, statements };
  };
  const files = new Map(); // file path -> promise of its text, most recently used last

  const sourceText = (filePath) => {
    let pending = files.get(filePath);
    files.delete(filePath);
    if (!pending) {
      pending = Promise.resolve().then(() => fetchSource(filePath));
      pending.catch(() => files.delete(filePath)); // do not remember failures
    }
    files.set(filePath, pending);
    if (files.size > CACHE_FILES) files.delete(files.keys().next().value);
    return pending;
  };

  // The declaration's statement as written in its source file on master.
  const source = async (name) => {
    const node = db.prepare('SELECT id, file_module FROM nodes WHERE name = ?').get(name);
    if (!node) return null;
    const filePath = modulePath(node.file_module);
    if (!filePath) return { found: false, reason: 'no_source_file' };
    // Start at the file the snapshot names; if it has since moved, follow its deprecation shim.
    let decl;
    try {
      decl = await locate(sourceText, filePath, name);
    } catch {
      return { found: false, reason: 'fetch_failed' };
    }
    if (decl.missing) return { found: false, reason: decl.missing };
    // Every direct dependency, so the page can link the names used in the text.
    const deps = db
      .prepare('SELECT n.name FROM edges e JOIN nodes n ON n.id = e.dst WHERE e.src = ? ORDER BY n.name')
      .all(node.id)
      .map((r) => r.name);
    const { path: foundIn, ...rest } = decl;
    return { found: true, ...rest, deps, url: `${GITHUB}${foundIn}#L${decl.line}` };
  };

  // For the declaration `focus`: of the `dependencies` given, which its statement mentions,
  // which only its proof uses, and which both do; and for each of the `dependents` given,
  // whether it mentions the focus in its own statement or only uses it in its proof.
  const where = (u, name) => {
    const inStatement = u.statement.includes(name), inProof = u.proof.includes(name);
    return inStatement && inProof ? 'both' : inStatement ? 'statement' : inProof ? 'proof' : null;
  };
  const usesOf = async (focus, dependencies, dependents) => {
    if (!lean) return { state: 'off', out: {}, in: {} };
    const names = (list) => [...new Set((Array.isArray(list) ? list : []).filter((n) => typeof n === 'string'))].slice(0, 400);
    const known = await lean.uses([focus, ...names(dependents)]);
    const out = {}, into = {};
    if (known[focus]) for (const dep of names(dependencies)) { const role = where(known[focus], dep); if (role) out[dep] = role; }
    for (const d of names(dependents)) { const role = known[d] && where(known[d], focus); if (role) into[d] = role; }
    return { state: lean.state, out, in: into };
  };

  // For each theorem among `names`: whether it holds by definition (its proof is reflexivity),
  // and the facts its proof rests on: the theorems it uses, plumbing set aside. One fact
  // means a corollary of it. `facts` is null when Lean has not said what the proof uses.
  const rolesOf = async (names) => {
    if (!lean) return { state: 'off', roles: {} };
    const wanted = [...new Set((Array.isArray(names) ? names : []).filter((n) => typeof n === 'string'))].slice(0, 400);
    const theorems = wanted.length
      ? db.prepare(`SELECT name FROM nodes WHERE kind = 'theorem' AND name IN (${wanted.map(() => '?').join(',')})`).all(...wanted).map((r) => r.name)
      : [];
    const [byRfl, used] = await Promise.all([lean.roles(theorems), lean.uses(theorems)]);
    const roles = {};
    for (const name of theorems) {
      if (!byRfl[name] && !used[name]) continue;
      roles[name] = {
        byDefinition: byRfl[name] ? byRfl[name].rfl : null,
        facts: used[name] ? facts(db, used[name].proof.filter((n) => n !== name)) : null,
      };
    }
    return { state: lean.state, roles };
  };

  const json = (res, status, body) => {
    res.writeHead(status, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store' });
    res.end(JSON.stringify(body));
  };

  const server = http.createServer((req, res) => {
    try {
      // Split by hand: the raw path must match exactly, so "/../x" can never reach a file.
      const [pathname, query = ''] = (req.url || '/').split('?');
      const params = new URLSearchParams(query);

      // POST /api/node takes the same options as the GET form in a JSON body, plus `pin`.
      if (req.method === 'POST' && (pathname === '/api/node' || pathname === '/api/elaborate' || pathname === '/api/uses' || pathname === '/api/roles')) {
        const chunks = [];
        let size = 0;
        req.on('data', (chunk) => {
          size += chunk.length;
          if (size <= MAX_BODY) chunks.push(chunk);
        });
        req.on('end', () => {
          try {
            if (size > MAX_BODY) return json(res, 413, { error: 'request too large' });
            let body;
            try {
              body = JSON.parse(Buffer.concat(chunks).toString('utf8'));
            } catch {
              return json(res, 400, { error: 'body must be JSON' });
            }
            if (pathname === '/api/roles') {
              if (!body || !Array.isArray(body.names)) return json(res, 400, { error: 'names must be a list' });
              return rolesOf(body.names).then((out) => json(res, 200, out), (err) => { console.error(err); json(res, 500, { error: 'internal error' }); });
            }
            if (pathname === '/api/uses') {
              if (!body || typeof body.focus !== 'string' || !body.focus) return json(res, 400, { error: 'focus is required' });
              return usesOf(body.focus, body.dependencies, body.dependents).then((out) => json(res, 200, out), (err) => { console.error(err); json(res, 500, { error: 'internal error' }); });
            }
            if (pathname === '/api/elaborate') {
              if (!body || !Array.isArray(body.names)) return json(res, 400, { error: 'names must be a list' });
              return elaborate(body.names).then((out) => json(res, 200, out), (err) => { console.error(err); json(res, 500, { error: 'internal error' }); });
            }
            if (!body || typeof body.name !== 'string' || !body.name) return json(res, 400, { error: 'name is required' });
            const result = neighborhood(db, body.name, {
              depth: body.depth ?? 1,
              explicit: body.explicit !== false && body.explicit !== 0,
              limit: body.limit ?? 25,
              pin: body.pin,
              hidePlumbing: body.plumbing === false || body.plumbing === 0,
              theoremsOnly: body.theorems === true || body.theorems === 1,
            });
            return result ? json(res, 200, answer(result)) : json(res, 404, { error: 'not found' });
          } catch (err) {
            console.error(err);
            json(res, 500, { error: 'internal error' });
          }
        });
        return;
      }
      if (req.method !== 'GET' && req.method !== 'HEAD') return json(res, 405, { error: 'method not allowed' });

      if (pathname === '/api/search') {
        return json(res, 200, withLean(search(db, params.get('q'), params.get('limit') ?? 20)));
      }
      if (pathname === '/api/node') {
        const name = params.get('name');
        if (!name) return json(res, 400, { error: 'name is required' });
        const result = neighborhood(db, name, {
          depth: params.get('depth') ?? 1,
          explicit: params.get('explicit') !== '0',
          limit: params.get('limit') ?? 25,
          hidePlumbing: params.get('plumbing') === '0',
          theoremsOnly: params.get('theorems') === '1',
        });
        return result ? json(res, 200, answer(result)) : json(res, 404, { error: 'not found' });
      }
      if (pathname === '/api/lean') return json(res, 200, { state: lean ? lean.state : 'off' });
      if (pathname === '/api/elaborate') return json(res, 405, { error: 'method not allowed' }); // POST only
      if (pathname === '/api/source') {
        const name = params.get('name');
        if (!name) return json(res, 400, { error: 'name is required' });
        return source(name).then(
          (result) => (result ? json(res, 200, result) : json(res, 404, { error: 'not found' })),
          (err) => { console.error(err); json(res, 500, { error: 'internal error' }); }
        );
      }
      if (Object.hasOwn(STATIC, pathname)) {
        const [file, type] = STATIC[pathname];
        res.writeHead(200, { 'content-type': type, 'cache-control': 'no-store' });
        return res.end(fs.readFileSync(path.join(PUBLIC, file)));
      }
      json(res, 404, { error: 'not found' });
    } catch (err) {
      console.error(err);
      json(res, 500, { error: 'internal error' });
    }
  });
  server.on('close', () => { db.close(); if (lean) lean.close().catch(() => {}); });
  return server;
}

module.exports = { createServer };

if (require.main === module) {
  const dbPath = path.join(__dirname, 'data', 'mathlib.db');
  if (!fs.existsSync(dbPath)) {
    console.error('Run "node build.js" first.');
    process.exit(1);
  }
  const port = Number(process.env.PORT) || 5173;
  // Read Lean files from the local checkout that build.js makes; without one, from GitHub.
  const checkout = path.join(__dirname, 'data', 'mathlib4');
  const fetchSource = fs.existsSync(path.join(checkout, 'Mathlib')) ? localSource(checkout) : fetchFromGitHub;
  // Lean itself, for statements with every inferred type filled in. It needs the compiled
  // Mathlib next to the checkout (`lake exe cache get` in data/mathlib4) and Lean's `lake`.
  const os = require('node:os');
  const elan = path.join(os.homedir(), '.elan', 'bin');
  const compiled = fs.existsSync(path.join(checkout, '.lake', 'build', 'lib'));
  const lean = new LeanStatements({
    cachePath: path.join(__dirname, 'data', 'lean-cache.v3.db'), // v3: scoped notation on, coercions printed with their type
    command: compiled ? (fs.existsSync(path.join(elan, 'lake')) ? path.join(elan, 'lake') : 'lake') : null,
    args: ['env', 'lean', '--run', path.join(__dirname, 'lean', 'Signatures.lean')],
    cwd: checkout,
    env: { ...process.env, PATH: `${elan}${path.delimiter}${process.env.PATH || ''}` },
  });
  if (compiled) {
    console.log('Lean: loading Mathlib in the background…');
    lean.start().then((ok) => console.log(ok ? 'Lean: ready.' : `Lean: could not start; statements come from the source text only.\n${lean.lastError || ''}`));
  } else console.log('Lean: not set up (no compiled Mathlib in data/mathlib4); statements come from the source text.');
  createServer(dbPath, { fetchSource, lean }).listen(port, '127.0.0.1', () => {
    console.log(`Mathlib graph navigator: http://127.0.0.1:${port}/`);
  });
}
