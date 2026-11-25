const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
const { open, search, neighborhood } = require('./lib/graphdb');
const { findDeclaration, modulePath, redirects } = require('./lib/leansource');

const GITHUB = 'https://github.com/leanprover-community/mathlib4/blob/master/';
const RAW = 'https://raw.githubusercontent.com/leanprover-community/mathlib4/master/';
const CACHE_FILES = 40;
const MAX_FILES_PER_LOOKUP = 6;
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
};

function createServer(dbPath, { fetchSource = fetchFromGitHub } = {}) {
  const db = open(dbPath);
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
    const queue = [filePath];
    const seen = new Set(queue);
    let first = true;
    while (queue.length && seen.size <= MAX_FILES_PER_LOOKUP) {
      const current = queue.shift();
      let text;
      try {
        text = await sourceText(current);
      } catch {
        return { found: false, reason: 'fetch_failed' };
      }
      if (text === null && first) return { found: false, reason: 'file_missing' };
      first = false;
      if (text === null) continue;
      const decl = findDeclaration(text, name);
      if (decl) {
        // Every direct dependency, so the page can link the names used in the text.
        const deps = db
          .prepare('SELECT n.name FROM edges e JOIN nodes n ON n.id = e.dst WHERE e.src = ? ORDER BY n.name')
          .all(node.id)
          .map((r) => r.name);
        return { found: true, ...decl, deps, url: `${GITHUB}${current}#L${decl.line}` };
      }
      for (const next of redirects(text)) {
        if (!seen.has(next)) { seen.add(next); queue.push(next); }
      }
    }
    return { found: false, reason: 'not_in_file' };
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
      if (req.method === 'POST' && pathname === '/api/node') {
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
            if (!body || typeof body.name !== 'string' || !body.name) return json(res, 400, { error: 'name is required' });
            const result = neighborhood(db, body.name, {
              depth: body.depth ?? 1,
              explicit: body.explicit !== false && body.explicit !== 0,
              limit: body.limit ?? 25,
              pin: body.pin,
              hidePlumbing: body.plumbing === false || body.plumbing === 0,
              theoremsOnly: body.theorems === true || body.theorems === 1,
            });
            return result ? json(res, 200, result) : json(res, 404, { error: 'not found' });
          } catch (err) {
            console.error(err);
            json(res, 500, { error: 'internal error' });
          }
        });
        return;
      }
      if (req.method !== 'GET' && req.method !== 'HEAD') return json(res, 405, { error: 'method not allowed' });

      if (pathname === '/api/search') {
        return json(res, 200, search(db, params.get('q'), params.get('limit') ?? 20));
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
        return result ? json(res, 200, result) : json(res, 404, { error: 'not found' });
      }
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
  server.on('close', () => db.close());
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
  createServer(dbPath).listen(port, '127.0.0.1', () => {
    console.log(`Mathlib graph navigator: http://127.0.0.1:${port}/`);
  });
}
