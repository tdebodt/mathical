const { test, before } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const { parseLine, rows } = require('../lib/csv');
const { buildDb, open } = require('../lib/graphdb');
const { buildFixtureDb, fixtures } = require('./helpers');

let db, res, dbPath;
before(async () => {
  ({ dbPath, res } = await buildFixtureDb());
  db = open(dbPath);
});

const edge = (s, d) =>
  db.prepare(
    `SELECT explicit FROM edges WHERE src=(SELECT id FROM nodes WHERE name=?)
     AND dst=(SELECT id FROM nodes WHERE name=?)`
  ).get(s, d);

test('parseLine handles quoted commas and escaped quotes', () => {
  assert.deepEqual(parseLine('a,"b,c","d""e",'), ['a', 'b,c', 'd"e', '']);
  assert.deepEqual(parseLine('x,y'), ['x', 'y']);
});

test('rows yields header-keyed objects', async () => {
  const out = [];
  for await (const r of rows(path.join(fixtures, 'edges.csv'))) out.push(r);
  assert.equal(out.length, 43);
  assert.deepEqual({ ...out[0] }, { source: 'Thm', target: 'A', is_explicit: 'True', is_simplifier: 'False' });
});

test('loads nodes and edges', () => {
  assert.equal(res.nodes, 44); // 43 in metrics + Ghost
  assert.equal(res.edges, 42); // 43 rows minus the C→C self-loop
  assert.equal(db.prepare('SELECT COUNT(*) c FROM nodes').get().c, 44);
  assert.equal(db.prepare('SELECT COUNT(*) c FROM edges').get().c, 42);
  assert.equal(edge('C', 'C'), undefined);
});

test('creates stub nodes for names missing from metrics', () => {
  const g = db.prepare('SELECT kind, pagerank FROM nodes WHERE name=?').get('Ghost');
  assert.equal(g.kind, null);
  assert.equal(g.pagerank, 0);
  assert.equal(res.stubs, 1);
});

test('stores explicit flag and booleans as integers, blanks as NULL', () => {
  assert.equal(edge('Thm', 'Hub').explicit, 0);
  assert.equal(edge('Thm', 'A').explicit, 1);
  const t = db.prepare('SELECT * FROM nodes WHERE name=?').get('Thm');
  assert.equal(t.is_tactic_proof, 1);
  assert.equal(t.tactic_count, 2);
  assert.equal(t.top_tactic, 'simp');
  assert.equal(t.instance_class, null);
  assert.equal(t.pagerank, 0.05);
});

test('rebuilding replaces an existing database', async () => {
  const again = await buildDb({
    edgesCsv: path.join(fixtures, 'edges.csv'),
    metricsCsv: path.join(fixtures, 'metrics.csv'),
    dbPath,
  });
  assert.equal(again.edges, 42);
  assert.equal(fs.existsSync(dbPath + '.tmp'), false);
  assert.equal(open(dbPath).prepare('SELECT COUNT(*) c FROM nodes').get().c, 44);
});
