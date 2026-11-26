const { test, before, after } = require('node:test');
const assert = require('node:assert/strict');
const http = require('node:http');
const { createServer } = require('../server');
const { buildFixtureDb } = require('./helpers');

let server, base, dbPathForSource;
before(async () => {
  const { dbPath } = await buildFixtureDb();
  dbPathForSource = dbPath;
  server = createServer(dbPath);
  await new Promise((r) => server.listen(0, '127.0.0.1', r));
  base = `http://127.0.0.1:${server.address().port}`;
});
after(() => server.close());

const get = async (p) => {
  const res = await fetch(base + p);
  const type = res.headers.get('content-type') || '';
  return { status: res.status, type, body: type.includes('json') ? await res.json() : await res.text() };
};

test('search endpoint', async () => {
  const r = await get('/api/search?q=Th');
  assert.equal(r.status, 200);
  assert.equal(r.type, 'application/json; charset=utf-8');
  assert.deepEqual(r.body.map((n) => n.name), ['Thm']);
  assert.deepEqual((await get('/api/search')).body, []);
});

test('node endpoint defaults to explicit depth 1', async () => {
  const r = await get('/api/node?name=Thm');
  assert.equal(r.status, 200);
  assert.deepEqual(r.body.out.nodes.map((n) => n.name), ['A', 'B', 'Ghost']);
  assert.equal(r.body.out.totals.length, 1);
});

test('explicit=0 and depth=2 are honoured', async () => {
  const r = await get('/api/node?name=Thm&explicit=0&depth=2&limit=50');
  const got = r.body.out.nodes.map((n) => n.name);
  assert.ok(got.includes('Hub'));
  assert.ok(got.includes('C'));
  assert.equal(r.body.out.totals.length, 2);
});

test('round-trips a URL-encoded unicode name', async () => {
  const r = await get('/api/node?name=%C2%ABterm_%E2%88%98_%C2%BB');
  assert.equal(r.status, 200);
  assert.equal(r.body.focus.name, '«term_∘_»');
  assert.equal((await get('/api/node?name=a%25b')).body.focus.name, 'a%b');
});

test('missing name is 400, unknown name is 404', async () => {
  const a = await get('/api/node');
  assert.equal(a.status, 400);
  assert.deepEqual(a.body, { error: 'name is required' });
  const b = await get('/api/node?name=Nope');
  assert.equal(b.status, 404);
  assert.deepEqual(b.body, { error: 'not found' });
});

test('non-numeric depth and limit fall back to defaults', async () => {
  const r = await get('/api/node?name=Hub&depth=abc&limit=xyz');
  assert.equal(r.status, 200);
  assert.equal(r.body.in.totals.length, 1);
  assert.equal(r.body.in.nodes.length, 25);
});

test('serves the page at / and 404s elsewhere', async () => {
  const r = await get('/');
  assert.equal(r.status, 200);
  assert.match(r.type, /text\/html/);
  assert.match(r.body, /Mathlib graph navigator/);
  assert.equal((await get('/nope')).status, 404);
  assert.equal((await get('/server.js')).status, 404);
  const js = await get('/lean.js');
  assert.equal(js.status, 200);
  assert.match(js.type, /javascript/);
  assert.equal((await get('/lean-latex.js')).status, 200);
  assert.equal((await get('/lean-phrases.js')).status, 200);
  assert.equal((await get('/lean-outline.js')).status, 200);
});

test('path traversal is refused', async () => {
  // fetch normalises "..", so send the raw path
  const status = await new Promise((resolve, reject) => {
    const { port } = server.address();
    http.get({ host: '127.0.0.1', port, path: '/../server.js' }, (res) => {
      res.resume();
      resolve(res.statusCode);
    }).on('error', reject);
  });
  assert.equal(status, 404);
});

test('malformed percent-encoding does not crash the server', async () => {
  const r = await get('/api/node?name=%E0%A4%A');
  assert.ok(r.status === 404 || r.status === 400);
  assert.equal((await get('/api/search?q=Th')).status, 200);
});

test('source endpoint returns the statement from the fetched file', async () => {
  const calls = [];
  const s = createServer(dbPathForSource, {
    fetchSource: async (p) => {
      calls.push(p);
      return p === 'Mathlib/Fix.lean' ? '/-- Doc. -/\ntheorem Thm (n : ℕ) : n = n := rfl\n' : null;
    },
  });
  await new Promise((r) => s.listen(0, '127.0.0.1', r));
  const at = `http://127.0.0.1:${s.address().port}`;
  try {
    const ok = await (await fetch(at + '/api/source?name=Thm')).json();
    assert.deepEqual(ok, {
      found: true,
      statement: 'theorem Thm (n : ℕ) : n = n',
      body: ':= rfl',
      context: '',
      deps: ['A', 'B', 'Ghost', 'Hub'],
      doc: 'Doc.',
      line: 2,
      url: 'https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Fix.lean#L2',
    });
    const miss = await (await fetch(at + '/api/source?name=A')).json();
    assert.deepEqual(miss, { found: false, reason: 'not_in_file' });
    assert.deepEqual(calls, ['Mathlib/Fix.lean']); // second request served from the cache
    const ghost = await (await fetch(at + '/api/source?name=Ghost')).json();
    assert.deepEqual(ghost, { found: false, reason: 'no_source_file' });
    assert.equal((await fetch(at + '/api/source?name=Nope')).status, 404);
    assert.equal((await fetch(at + '/api/source')).status, 400);
  } finally {
    s.close();
  }
});

test('source endpoint reports a failed download without crashing', async () => {
  const s = createServer(dbPathForSource, { fetchSource: async () => { throw new Error('offline'); } });
  await new Promise((r) => s.listen(0, '127.0.0.1', r));
  try {
    const res = await fetch(`http://127.0.0.1:${s.address().port}/api/source?name=Thm`);
    assert.equal(res.status, 200);
    assert.deepEqual(await res.json(), { found: false, reason: 'fetch_failed' });
  } finally {
    s.close();
  }
});

test('source endpoint follows a moved file through its deprecated shim', async () => {
  const filesOnMaster = {
    'Mathlib/Fix.lean': 'module\n\nimport Mathlib.New.Home\n\ndeprecated_module (since := "2026-05-28")\n',
    'Mathlib/New/Home.lean': '\ntheorem Thm : True := trivial\n',
  };
  const s = createServer(dbPathForSource, { fetchSource: async (p) => filesOnMaster[p] ?? null });
  await new Promise((r) => s.listen(0, '127.0.0.1', r));
  try {
    const at = `http://127.0.0.1:${s.address().port}`;
    const r = await (await fetch(at + '/api/source?name=Thm')).json();
    assert.equal(r.statement, 'theorem Thm : True');
    assert.equal(r.url, 'https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/New/Home.lean#L2');
    assert.deepEqual(await (await fetch(at + '/api/source?name=B')).json(), { found: false, reason: 'not_in_file' });
  } finally {
    s.close();
  }
});

test('POST /api/node accepts a list of names to pin', async () => {
  const post = (body) => fetch(base + '/api/node', { method: 'POST', body: typeof body === 'string' ? body : JSON.stringify(body) });
  const res = await post({ name: 'Thm', limit: 1, pin: ['Ghost'] });
  assert.equal(res.status, 200);
  assert.deepEqual((await res.json()).out.nodes.map((n) => n.name), ['Ghost', 'A']);
  assert.equal((await post('{not json')).status, 400);
  assert.equal((await post({ limit: 1 })).status, 400);
  assert.equal((await post({ name: 'Nope' })).status, 404);
  assert.equal((await post({ name: 'Thm', pin: 'x'.repeat(300000) })).status, 413);
  assert.equal((await fetch(base + '/api/search?q=Th', { method: 'POST' })).status, 405);
});

test('plumbing=0 hides Lean core plumbing; the default shows everything', async () => {
  assert.deepEqual((await get('/api/node?name=Core')).body.out.nodes.map((n) => n.name), ['Eq.mpr', 'axb', 'Nat.succ']);
  const tidy = (await get('/api/node?name=Core&plumbing=0')).body.out;
  assert.deepEqual(tidy.nodes.map((n) => n.name), ['axb', 'Nat.succ']);
  assert.deepEqual(tidy.hidden, [1]);
  const res = await fetch(base + '/api/node', { method: 'POST', body: JSON.stringify({ name: 'Core', plumbing: false }) });
  assert.deepEqual((await res.json()).out.nodes.map((n) => n.name), ['axb', 'Nat.succ']);
});

test('theorems=1 keeps only theorems', async () => {
  const out = (await get('/api/node?name=Thm&theorems=1')).body.out;
  assert.deepEqual(out.nodes.map((n) => n.name), ['A', 'B']);
  assert.deepEqual(out.hidden, [1]);
  const res = await fetch(base + '/api/node', { method: 'POST', body: JSON.stringify({ name: 'Thm', theorems: true }) });
  assert.deepEqual((await res.json()).out.nodes.map((n) => n.name), ['A', 'B']);
});

test('with Lean: elaborated statements are fetched on demand, then come with the nodes', async () => {
  const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
  const { LeanStatements } = require('../lib/lean');
  const cachePath = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'mathical-srv-lean-')), 'cache.db');
  const lean = new LeanStatements({ cachePath, command: process.execPath, args: [path.join(__dirname, 'fixtures', 'fake-lean.js')] });
  const s = createServer(dbPathForSource, { lean });
  await new Promise((r) => s.listen(0, '127.0.0.1', r));
  const at = `http://127.0.0.1:${s.address().port}`;
  const json = async (p, init) => (await fetch(at + p, init)).json();
  try {
    assert.equal((await json('/api/node?name=Thm')).focus.lean, undefined); // nothing known yet
    const got = await json('/api/elaborate', { method: 'POST', body: JSON.stringify({ names: ['Thm', 'Hub', 'A', 'NotANode'] }) });
    assert.equal(got.state, 'ready');
    assert.deepEqual(got.statements, {
      Thm: 'theorem Thm {α : Type u_1} [Field α] (x : α) (h : x ≠ 0) : x / x = 1',
      Hub: 'def Hub {α : Type u_1} [Field α] (x : α) : α',
    });
    // from now on the node rows carry it
    const node = await json('/api/node?name=Thm&explicit=0');
    assert.equal(node.focus.lean, got.statements.Thm);
    assert.equal(node.out.nodes.find((n) => n.name === 'Hub').lean, got.statements.Hub);
    assert.equal(node.out.nodes.find((n) => n.name === 'A').lean, undefined);
    assert.equal((await json('/api/search?q=Hub'))[0].lean, got.statements.Hub);
    assert.deepEqual(await json('/api/lean'), { state: 'ready' });
    assert.equal((await fetch(at + '/api/elaborate', { method: 'POST', body: '{"names":"Thm"}' })).status, 400);
    assert.equal((await fetch(at + '/api/elaborate')).status, 405);
  } finally {
    await new Promise((r) => s.close(r));
  }
});

test('without Lean: the elaborate endpoint answers empty and nodes are as before', async () => {
  const got = await (await fetch(base + '/api/elaborate', { method: 'POST', body: JSON.stringify({ names: ['Thm'] }) })).json();
  assert.deepEqual(got, { state: 'off', statements: {} });
  assert.deepEqual(await (await fetch(base + '/api/lean')).json(), { state: 'off' });
  assert.equal('lean' in (await get('/api/node?name=Thm')).body.focus, false);
});

test('with Lean: whether a dependency is used by the statement, the proof, or both', async () => {
  const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
  const { LeanStatements } = require('../lib/lean');
  const cachePath = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'mathical-srv-uses-')), 'cache.db');
  const lean = new LeanStatements({ cachePath, command: process.execPath, args: [path.join(__dirname, 'fixtures', 'fake-lean.js')] });
  const s = createServer(dbPathForSource, { lean });
  await new Promise((r) => s.listen(0, '127.0.0.1', r));
  const post = async (body) => (await fetch(`http://127.0.0.1:${s.address().port}/api/uses`, { method: 'POST', body: JSON.stringify(body) })).json();
  try {
    // Thm's statement mentions Hub; its proof uses A, B and Hub again
    assert.deepEqual(await post({ focus: 'Thm', dependencies: ['A', 'Hub', 'Ghost'], dependents: [] }),
      { state: 'ready', out: { A: 'proof', Hub: 'both' }, in: {} });
    // seen from Hub: L1 states something about it, L2 only uses it to prove something else
    assert.deepEqual(await post({ focus: 'Hub', dependencies: [], dependents: ['L1', 'L2', 'L3'] }),
      { state: 'ready', out: {}, in: { L1: 'statement', L2: 'proof' } });
    assert.equal((await fetch(`http://127.0.0.1:${s.address().port}/api/uses`, { method: 'POST', body: '{}' })).status, 400);
  } finally {
    await new Promise((r) => s.close(r));
  }
});

test('without Lean: the uses endpoint answers empty', async () => {
  const got = await (await fetch(base + '/api/uses', { method: 'POST', body: JSON.stringify({ focus: 'Thm', dependencies: ['A'], dependents: [] }) })).json();
  assert.deepEqual(got, { state: 'off', out: {}, in: {} });
});

test('with Lean: what a theorem rests on, and whether it holds by definition', async () => {
  const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
  const { LeanStatements } = require('../lib/lean');
  const cachePath = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'mathical-srv-roles-')), 'cache.db');
  const lean = new LeanStatements({ cachePath, command: process.execPath, args: [path.join(__dirname, 'fixtures', 'fake-lean.js')] });
  const s = createServer(dbPathForSource, { lean });
  await new Promise((r) => s.listen(0, '127.0.0.1', r));
  const post = async (body) => fetch(`http://127.0.0.1:${s.address().port}/api/roles`, { method: 'POST', body: JSON.stringify(body) });
  try {
    // Thm's proof uses the theorems A and B, and the definition Hub, which is not a fact
    assert.deepEqual(await (await post({ names: ['Thm', 'A', 'Hub', 'NotANode'] })).json(), {
      state: 'ready',
      roles: { Thm: { byDefinition: false, facts: ['A', 'B'], main: null }, A: { byDefinition: true, facts: null, main: null } },
    });
    // a proof resting on one result: how widely used that result is, whether it has an argument of
    // its own (how many facts it rests on), and whether this theorem merely says the same thing again
    const single = (await (await post({ names: ['Core', 'UsesRing'] })).json()).roles;
    assert.deepEqual(single.Core, { byDefinition: null, facts: ['Thm'], main: { name: 'Thm', uses: 1, facts: 2, same: false } });
    assert.deepEqual(single.UsesRing.main, { name: 'Thm', uses: 1, facts: 2, same: true });
    assert.equal((await post({})).status, 400);
  } finally {
    await new Promise((r) => s.close(r));
  }
});

test('without Lean: the roles endpoint answers empty', async () => {
  const got = await (await fetch(base + '/api/roles', { method: 'POST', body: JSON.stringify({ names: ['Thm'] }) })).json();
  assert.deepEqual(got, { state: 'off', roles: {} });
});

test('with Lean: the steps of a proof, each with what it leaves to prove', async () => {
  const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
  const { LeanStatements } = require('../lib/lean');
  const { localSource } = require('../lib/leansource');
  const dbPath = dbPathForSource;
  const cachePath = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'mathlib-graph-')), 'lean.db');
  const fixtures = path.join(__dirname, 'fixtures');
  const lean = new LeanStatements({
    cachePath, command: process.execPath, args: [path.join(fixtures, 'fake-lean.js')], stepsArgs: [path.join(fixtures, 'fake-steps.js'), 'ok'],
  });
  const server = createServer(dbPath, { fetchSource: localSource(path.join(fixtures, 'src')), lean });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  const base = `http://127.0.0.1:${server.address().port}`;
  try {
    const got = await (await fetch(`${base}/api/steps?name=Thm`)).json();
    assert.equal(got.found, true);
    assert.equal(got.proof.goal, 'n + 0 = n');
    assert.deepEqual(got.proof.steps.map((s) => [s.text, s.results[0].target, s.closes]), [['add_zero', 'n = n', true]]);
    assert.deepEqual(await (await fetch(`${base}/api/steps?name=Hub`)).json(), { found: false, reason: 'no_steps' });
    assert.equal((await fetch(`${base}/api/steps?name=Missing`)).status, 404);
    assert.equal((await fetch(`${base}/api/steps`)).status, 400);
  } finally {
    await new Promise((resolve) => server.close(resolve)); // closes Lean too
  }
});

test('without Lean: no steps, and the page is told why', async () => {
  const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
  const { LeanStatements } = require('../lib/lean');
  const { localSource } = require('../lib/leansource');
  const dbPath = dbPathForSource;
  const cachePath = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'mathlib-graph-')), 'lean.db');
  const lean = new LeanStatements({ cachePath });
  const server = createServer(dbPath, { fetchSource: localSource(path.join(__dirname, 'fixtures', 'src')), lean });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  try {
    const got = await (await fetch(`http://127.0.0.1:${server.address().port}/api/steps?name=Thm`)).json();
    assert.deepEqual(got, { found: false, reason: 'no_lean' });
  } finally {
    await new Promise((resolve) => server.close(resolve)); // closes Lean too
  }
});
