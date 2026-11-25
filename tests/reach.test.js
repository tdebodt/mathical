const { test } = require('node:test');
const assert = require('node:assert/strict');
const { computeReach } = require('../lib/reach');
const { open } = require('../lib/graphdb');
const { buildFixtureDb } = require('./helpers');

// Exact answer by brute force: everything that depends on `v`, directly or not.
function exact(n, src, dst) {
  const users = Array.from({ length: n }, () => []);
  for (let e = 0; e < src.length; e++) users[dst[e]].push(src[e]);
  return Array.from({ length: n }, (_, v) => {
    const seen = new Set([v]);
    const stack = [v];
    while (stack.length) for (const u of users[stack.pop()]) if (!seen.has(u)) { seen.add(u); stack.push(u); }
    return seen.size - 1;
  });
}

test('a chain, a diamond and a leaf are counted exactly', () => {
  // 0 → 1 → 2 → 3 (each depends on the next), 4 → 2, 5 alone
  const src = Int32Array.from([0, 1, 2, 4]), dst = Int32Array.from([1, 2, 3, 2]);
  assert.deepEqual([...computeReach(6, src, dst)], [0, 1, 3, 4, 0, 0]);
});

test('cycles and duplicate edges do not double count', () => {
  // 0 → 1 → 2 → 0 is a cycle; 3 → 0; the edge 3 → 0 appears twice
  const src = Int32Array.from([0, 1, 2, 3, 3]), dst = Int32Array.from([1, 2, 0, 0, 0]);
  assert.deepEqual([...computeReach(4, src, dst)], [3, 3, 3, 0]);
});

test('on a random graph the estimate stays close to the exact count', () => {
  const n = 4000, src = [], dst = [];
  let seed = 12345;
  const rand = () => ((seed = (Math.imul(seed, 1103515245) + 12345) >>> 0) / 4294967296);
  for (let u = 1; u < n; u++) for (let k = 0; k < 3; k++) { src.push(u); dst.push(Math.floor(rand() * u)); } // u depends on earlier nodes
  const got = computeReach(n, Int32Array.from(src), Int32Array.from(dst));
  const want = exact(n, src, dst);
  let worst = 0;
  for (let v = 0; v < n; v++) {
    if (want[v] === 0) assert.equal(got[v], 0, `node ${v} is a leaf`);
    else worst = Math.max(worst, Math.abs(got[v] - want[v]) / Math.max(want[v], 20));
  }
  assert.ok(worst < 0.12, `worst relative error ${worst}`);
  assert.ok(want[0] > 3000 && Math.abs(got[0] - want[0]) / want[0] < 0.08);
});

test('the build stores each declaration\'s reach', async () => {
  const db = open((await buildFixtureDb()).dbPath);
  const reach = (name) => db.prepare('SELECT reach FROM nodes WHERE name = ?').get(name).reach;
  assert.equal(reach('Thm'), 0); // nothing depends on it
  assert.equal(reach('L7'), 0);
  assert.equal(reach('Hub'), 31); // L1…L30 and Thm
  assert.equal(reach('Eq.mpr'), 1); // Core
  assert.equal(reach('C'), 4); // A, B, D (through the cycle) and Thm
  assert.equal(reach('Ghost'), 1); // Thm
});
