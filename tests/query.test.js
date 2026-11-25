const { test, before } = require('node:test');
const assert = require('node:assert/strict');
const { open, search, neighborhood } = require('../lib/graphdb');
const { buildFixtureDb } = require('./helpers');

let db;
before(async () => {
  db = open((await buildFixtureDb()).dbPath);
});

const names = (side) => side.nodes.map((n) => n.name);
const id = (name) => db.prepare('SELECT id FROM nodes WHERE name=?').get(name).id;

test('direct explicit dependencies', () => {
  const r = neighborhood(db, 'Thm');
  assert.equal(r.focus.name, 'Thm');
  assert.deepEqual(names(r.out), ['A', 'B', 'Ghost']); // pagerank order, stub last
  assert.deepEqual(r.out.totals, [3]);
  assert.deepEqual(names(r.in), []);
  assert.deepEqual(r.in.totals, [0]);
  assert.equal(r.out.edges.length, 4); // Thm→A, Thm→B, Thm→Ghost, A→B
});

test('explicit=false adds synthesized edges', () => {
  const r = neighborhood(db, 'Thm', { explicit: false });
  assert.ok(names(r.out).includes('Hub'));
  assert.ok(r.out.edges.some(([s, d, e]) => s === id('Thm') && d === id('Hub') && e === 0));
});

test('dependents come back on the in side', () => {
  const r = neighborhood(db, 'C');
  assert.deepEqual(names(r.in), ['A', 'B']);
  assert.deepEqual(names(r.out), ['D']);
});

test('caps a large side and reports the total', () => {
  const r = neighborhood(db, 'Hub', { limit: 10 });
  assert.equal(r.in.nodes.length, 10);
  assert.deepEqual(r.in.totals, [30]);
  assert.equal(r.in.nodes[0].name, 'L1');
});

test('nodes cut by the cap do not reappear at a deeper level', () => {
  // A depends on B, and B is cut by the cap at distance 1: it must not come back at distance 2
  const r = neighborhood(db, 'Thm', { depth: 2, limit: 1 });
  assert.deepEqual(r.out.nodes.map((n) => [n.name, n.dist]), [['A', 1], ['C', 2]]);
  assert.deepEqual(r.out.totals, [3, 1]);
});

test('handles cycles', () => {
  const r = neighborhood(db, 'A', { depth: 3 });
  assert.deepEqual(r.out.nodes.map((n) => [n.name, n.dist]), [['B', 1], ['C', 1], ['D', 2]]);
  assert.ok(r.out.edges.some(([s, d]) => s === id('D') && d === id('A')));
  assert.deepEqual(r.out.totals, [2, 1, 0]);
  // the same cycle walked backwards: D is used by C, C by A and B, then Thm
  const back = neighborhood(db, 'D', { depth: 3 });
  assert.deepEqual(back.in.nodes.map((n) => [n.name, n.dist]), [['C', 1], ['A', 2], ['B', 2], ['Thm', 3]]);
});

test('depth and limit are clamped', () => {
  assert.equal(neighborhood(db, 'A', { depth: 99 }).out.totals.length, 3);
  assert.equal(neighborhood(db, 'A', { depth: 0 }).out.totals.length, 1);
  assert.equal(neighborhood(db, 'Hub', { limit: 0 }).in.nodes.length, 1);
  assert.equal(neighborhood(db, 'Hub', { limit: NaN }).in.nodes.length, 25);
});

test('says whether the additive pair exists in the graph', () => {
  assert.equal(neighborhood(db, 'Thm').focus.pair_exists, true);
  assert.equal(neighborhood(db, 'A').focus.pair_exists, false);
  assert.equal(neighborhood(db, 'B').focus.pair_exists, false);
});

test('limit is capped at 200', () => {
  assert.equal(neighborhood(db, 'Hub', { limit: 5000 }).in.nodes.length, 30);
});

test('unknown name returns null', () => assert.equal(neighborhood(db, 'Nope'), null));

test('search ranks exact, then prefix, then substring', () => {
  const r = search(db, 'a').map((n) => n.name);
  assert.equal(r[0], 'A');
  assert.deepEqual(r.slice(1, 4), ['a%b', 'a_b', 'axb']);
  assert.equal(search(db, 'a', 2).length, 2);
});

test('search treats % and _ literally', () => {
  assert.deepEqual(search(db, 'a%b').map((n) => n.name), ['a%b']);
  assert.deepEqual(search(db, 'a_b').map((n) => n.name), ['a_b']);
});

test('search finds unicode names and returns [] for blank', () => {
  assert.equal(search(db, '∘')[0].name, '«term_∘_»');
  assert.deepEqual(search(db, '  '), []);
});

test('pinned dependencies are always drawn, ahead of the cap', () => {
  const r = neighborhood(db, 'Thm', { limit: 1, pin: ['Ghost', 'B', 'D', 'Hub', 'Nope'] });
  // B and Ghost are direct explicit dependencies; D is not one, Hub is not explicit, Nope does not exist
  assert.deepEqual(r.out.nodes.map((n) => [n.name, !!n.pinned]), [['B', true], ['Ghost', true], ['A', false]]);
  assert.deepEqual(r.out.totals, [3]);
  assert.equal(r.out.edges.length, 4);
  const all = neighborhood(db, 'Thm', { explicit: false, limit: 1, pin: ['Hub'] });
  assert.deepEqual(all.out.nodes.map((n) => n.name), ['Hub']); // already the top-ranked one: listed once
  assert.deepEqual(neighborhood(db, 'Thm', { limit: 1, pin: [] }).out.nodes.map((n) => n.name), ['A']);
});

test('pins do not leak into deeper levels or the other side', () => {
  const r = neighborhood(db, 'Thm', { depth: 2, limit: 1, pin: ['B'] });
  assert.deepEqual(r.out.nodes.map((n) => [n.name, n.dist]), [['B', 1], ['A', 1], ['C', 2]]);
  assert.deepEqual(neighborhood(db, 'C', { limit: 1, pin: ['B'] }).in.nodes.map((n) => n.name), ['A']);
});

test('hidePlumbing leaves out Lean core logic and notation, but keeps core data such as Nat', () => {
  const all = neighborhood(db, 'Core');
  assert.deepEqual(names(all.out), ['Eq.mpr', 'axb', 'Nat.succ']);
  assert.deepEqual(all.out.hidden, [0]);
  const tidy = neighborhood(db, 'Core', { hidePlumbing: true });
  assert.deepEqual(names(tidy.out), ['axb', 'Nat.succ']);
  assert.deepEqual(tidy.out.totals, [2]);
  assert.deepEqual(tidy.out.hidden, [1]);
  assert.equal(tidy.out.edges.length, 2);
  // a pin does not bring plumbing back, and a declaration without metadata is not plumbing
  assert.deepEqual(names(neighborhood(db, 'Core', { hidePlumbing: true, pin: ['Eq.mpr'] }).out), ['axb', 'Nat.succ']);
  assert.ok(names(neighborhood(db, 'Thm', { hidePlumbing: true }).out).includes('Ghost'));
});

test('hidePlumbing never hides the focus itself', () => {
  const r = neighborhood(db, 'Eq.mpr', { hidePlumbing: true });
  assert.equal(r.focus.name, 'Eq.mpr');
  assert.deepEqual(names(r.in), ['Core']);
});

test('theoremsOnly keeps only theorems among the neighbours', () => {
  const r = neighborhood(db, 'Thm', { theoremsOnly: true });
  assert.deepEqual(names(r.out), ['A', 'B']); // Ghost has no kind
  assert.deepEqual(r.out.totals, [2]);
  assert.deepEqual(r.out.hidden, [1]);
  const all = neighborhood(db, 'Thm', { theoremsOnly: true, explicit: false });
  assert.deepEqual(names(all.out), ['A', 'B']); // Hub is a definition
  assert.deepEqual(all.out.hidden, [2]);
  // the focus may be a definition, and both filters combine
  assert.equal(neighborhood(db, 'Hub', { theoremsOnly: true, limit: 5 }).in.nodes.length, 5);
  const both = neighborhood(db, 'Core', { theoremsOnly: true, hidePlumbing: true });
  assert.deepEqual(names(both.out), ['axb', 'Nat.succ']);
  assert.deepEqual(both.out.hidden, [1]);
  assert.deepEqual(names(neighborhood(db, 'Thm', { theoremsOnly: true, pin: ['Ghost'] }).out), ['A', 'B']);
});
