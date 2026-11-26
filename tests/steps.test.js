const test = require('node:test');
const assert = require('node:assert/strict');
const { arrange } = require('../lib/steps');

// What lean/Steps.lean reports, in its order (inner steps before the blocks that hold them).
const goal = (id, target, hyps = [['x', 'ℝ']]) => ({
  id, case: '', target,
  hyps: hyps.map(([name, type, prop = false, inst = false]) => ({ name, type, prop, inst })),
});
const step = (start, stop, kind, text, before, after) => ({ start, stop, kind, text, before, after });

test('a chain of rewrites: one step per rule, each with the goal it leaves', () => {
  const g0 = goal('g0', 'tan (↑x) = tan x'), g1 = goal('g1', 'sin (↑x) / cos (↑x) = tan x');
  const g2 = goal('g2', 'sin x / cos x = tan x'), g3 = goal('g3', 'sin x / cos x = sin x / cos x');
  const proof = arrange([
    step(9, 13, 'null', 'tan,', [g0], [g1]),
    step(14, 22, 'null', 'sin_coe,', [g1], [g2]),
    step(23, 30, 'null', 'tan_def', [g2], [g3]),
    step(30, 31, '«]»', ']', [g3], []),
    step(5, 31, 'Lean.Parser.Tactic.rwSeq', 'rw [tan, sin_coe, tan_def]', [g0], []),
    step(5, 31, 'Lean.Parser.Tactic.tacticSeq1Indented', 'rw [tan, sin_coe, tan_def]', [g0], []),
    step(5, 31, 'Lean.Parser.Tactic.tacticSeq', 'rw [tan, sin_coe, tan_def]', [g0], []),
    step(0, 2, 'by', 'by', [g0], []),
    step(0, 31, 'Lean.Parser.Term.byTactic', 'by\n  rw [tan, sin_coe, tan_def]', [g0], []),
  ]);
  assert.equal(proof.goal, 'tan (↑x) = tan x');
  assert.deepEqual(proof.given, [{ name: 'x', type: 'ℝ', prop: false }]);
  assert.deepEqual(proof.steps.map((s) => s.text), ['tan', 'sin_coe', 'tan_def']);
  assert.deepEqual(proof.steps.map((s) => s.rewrite), [true, true, true]);
  assert.deepEqual(proof.steps.map((s) => s.results.map((r) => r.target)), [
    ['sin (↑x) / cos (↑x) = tan x'], ['sin x / cos x = tan x'], ['sin x / cos x = sin x / cos x'],
  ]);
  // the closing bracket checked that both sides are the same: said on the last rule, not as a step
  assert.deepEqual(proof.steps.map((s) => s.closes), [false, false, true]);
  assert.deepEqual(proof.steps.map((s) => s.depth), [0, 0, 0]);
});

test('a step recorded twice under two names is shown once; what it introduces is listed', () => {
  const g0 = goal('g0', '∀ θ, f θ = 0', []), g1 = goal('g1', 'f θ = 0', [['θ', 'Angle']]);
  const proof = arrange([
    step(3, 10, 'null', 'intro θ', [g0], [g1]),
    step(3, 10, 'Lean.Parser.Tactic.intro', 'intro θ', [g0], [g1]),
    step(11, 20, 'Lean.Parser.Tactic.exact', 'exact foo', [g1], []),
    step(0, 20, 'Lean.Parser.Term.byTactic', 'by intro θ\n exact foo', [g0], []),
  ]);
  assert.deepEqual(proof.steps.map((s) => s.text), ['intro θ', 'exact foo']);
  assert.deepEqual(proof.steps[0].results, [{ target: 'f θ = 0', learned: [{ name: 'θ', type: 'Angle', prop: false }] }]);
  assert.equal(proof.steps[0].rewrite, false);
  assert.deepEqual(proof.steps[1].results, []);
  assert.equal(proof.steps[1].closes, true);
});

test('cases: a split lists its cases, a bullet opens one, and its steps sit under it', () => {
  const g0 = goal('g0', 'a ↔ b'), l = goal('l', 'a → b'), r = goal('r', 'b → a');
  const l1 = goal('l1', 'b', [['x', 'ℝ'], ['h', 'a', true]]);
  const proof = arrange([
    step(3, 14, 'Lean.Parser.Tactic.constructor', 'constructor', [g0], [l, r]),
    step(17, 18, 'Lean.cdotTk', '·', [l, r], [l]),
    step(19, 26, 'Lean.Parser.Tactic.intro', 'intro h', [l], [l1]),
    step(29, 36, 'Lean.Parser.Tactic.exact', 'exact f h', [l1], []),
    step(19, 36, 'Lean.Parser.Tactic.tacticSeq', 'intro h\n  exact f h', [l], []),
    step(17, 36, 'Lean.cdot', '· intro h\n  exact f h', [l, r], [r]),
    step(39, 40, 'Lean.cdotTk', '·', [r], [r]),
    step(41, 48, 'Lean.Parser.Tactic.exact', 'exact g', [r], []),
    step(39, 48, 'Lean.cdot', '· exact g', [r], []),
    step(0, 48, 'Lean.Parser.Term.byTactic', 'by …', [g0], []),
  ]);
  assert.deepEqual(proof.steps.map((s) => [s.kind, s.depth, s.text]), [
    ['step', 0, 'constructor'], ['case', 0, '·'], ['step', 1, 'intro h'], ['step', 1, 'exact f h'], ['case', 0, '·'], ['step', 1, 'exact g'],
  ]);
  assert.deepEqual(proof.steps[0].results.map((x) => x.target), ['a → b', 'b → a']);
  assert.deepEqual(proof.steps[1].results, [{ target: 'a → b', learned: [] }]);
  assert.deepEqual(proof.steps[2].results, [{ target: 'b', learned: [{ name: 'h', type: 'a', prop: true }] }]);
});

test('a rewrite of a hypothesis: the goal is unchanged, the hypothesis is what is new', () => {
  const g0 = goal('g0', 'P', [['h', 'a = b', true]]), g1 = goal('g1', 'P', [['h', 'b = a', true]]);
  const proof = arrange([
    step(4, 11, 'null', 'eq_comm', [g0], [g1]),
    step(11, 12, '«]»', ']', [g1], [g1]),
    step(0, 17, 'Lean.Parser.Tactic.rwSeq', 'rw [eq_comm] at h', [g0], [g1]),
    step(0, 17, 'Lean.Parser.Term.byTactic', 'rw [eq_comm] at h', [g0], [g1]),
  ]);
  assert.equal(proof.steps.length, 1);
  assert.equal(proof.steps[0].at, 'h');
  assert.deepEqual(proof.steps[0].results, [{ target: null, learned: [{ name: 'h', type: 'b = a', prop: true }] }]);
  assert.equal(proof.steps[0].closes, false);
});

test('a step that holds a proof of its own keeps only its first line; instance hypotheses are not listed', () => {
  const g0 = goal('g0', 'Q', [['inst', 'Field α', false, true], ['x', 'α']]);
  const sub = goal('s', '0 < é', [['inst', 'Field α', false, true], ['x', 'α']]);
  const g1 = goal('g1', 'Q', [['inst', 'Field α', false, true], ['x', 'α'], ['h', '0 < é', true]]);
  const text = 'have h : 0 < é := by\n  simp';
  const at = Buffer.byteLength('have h : 0 < é := by\n  '); // positions are in bytes, as Lean counts
  const proof = arrange([
    step(at, at + 4, 'Lean.Parser.Tactic.simp', 'simp', [sub], []),
    step(at - 5, at + 4, 'Lean.Parser.Term.byTactic', 'by\n  simp', [sub], []),
    step(0, at + 4, 'Lean.Parser.Tactic.tacticHave__', text, [g0], [g1]),
    step(0, at + 4, 'Lean.Parser.Term.byTactic', text, [g0], [g1]),
  ]);
  assert.deepEqual(proof.given, [{ name: 'x', type: 'α', prop: false }]);
  assert.deepEqual(proof.steps.map((s) => [s.depth, s.text]), [[0, 'have h : 0 < é := by'], [1, 'simp']]);
  assert.deepEqual(proof.steps[0].results, [{ target: null, learned: [{ name: 'h', type: '0 < é', prop: true }] }]);
});

test('nothing recorded: no steps to show', () => {
  assert.equal(arrange([]), null);
  assert.equal(arrange(null), null);
});
