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
  // each bullet says which case it opens, of how many
  assert.deepEqual(proof.steps.filter((s) => s.kind === 'case').map((s) => [s.number, s.of]), [[1, 2], [2, 2]]);
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

test('cases inside a case are numbered under it: 1.1, 1.2, so two "case 1" are never confused', () => {
  const g = goal('g', 'a ↔ b'), l = goal('l', 'a → b'), r = goal('r', 'b → a');
  const l1 = goal('l1', 'b', [['h', 'p', true]]), l2 = goal('l2', 'b', [['h', 'q', true]]);
  const proof = arrange([
    step(0, 11, 'Lean.Parser.Tactic.constructor', 'constructor', [g], [l, r]),
    step(12, 13, 'Lean.cdotTk', '·', [l, r], [l]),
    step(14, 22, 'Lean.Parser.Tactic.rcases', 'rcases h', [l], [l1, l2]),
    step(25, 26, 'Lean.cdotTk', '·', [l1, l2], [l1]),
    step(27, 34, 'Lean.Parser.Tactic.exact', 'exact x', [l1], []),
    step(25, 34, 'Lean.cdot', '· exact x', [l1, l2], [l2]),
    step(37, 38, 'Lean.cdotTk', '·', [l2], [l2]),
    step(39, 46, 'Lean.Parser.Tactic.exact', 'exact y', [l2], []),
    step(37, 46, 'Lean.cdot', '· exact y', [l2], []),
    step(14, 46, 'Lean.Parser.Tactic.tacticSeq', 'rcases h …', [l], []),
    step(12, 46, 'Lean.cdot', '· rcases h …', [l, r], [r]),
    step(49, 50, 'Lean.cdotTk', '·', [r], [r]),
    step(51, 58, 'Lean.Parser.Tactic.exact', 'exact z', [r], []),
    step(49, 58, 'Lean.cdot', '· exact z', [r], []),
    step(0, 58, 'Lean.Parser.Term.byTactic', 'by …', [g], []),
  ]);
  assert.deepEqual(proof.steps.filter((s) => s.kind === 'case').map((s) => s.label), ['1', '1.1', '1.2', '2']);
  // a case opens with what is known in it beyond what the proof started with
  const opened = proof.steps.filter((s) => s.kind === 'case');
  assert.deepEqual(opened[2].results, [{ target: 'b', learned: [{ name: 'h', type: 'q', prop: true }] }]);
  assert.deepEqual(opened[0].results, [{ target: 'a → b', learned: [] }]);
  // a step says which case it is in, so the cases it splits into can be numbered under it
  assert.equal(proof.steps.find((s) => s.text === 'constructor').within, '');
  assert.equal(proof.steps.find((s) => s.text === 'rcases h').within, '1');
  assert.equal(proof.steps.find((s) => s.text === 'exact y').within, '1.2');
});

test('a case the proof does not mark gets its heading all the same, from the goal Lean works on', () => {
  const g = goal('g', 'a ↔ b'), l = goal('l', 'a → b'), r = goal('r', 'b → a');
  const r1 = goal('r1', 'a', [['x', 'ℝ'], ['h', 'b', true]]);
  const proof = arrange([
    step(0, 11, 'Lean.Parser.Tactic.constructor', 'constructor', [g], [l, r]),
    step(12, 13, 'Lean.cdotTk', '·', [l, r], [l]),
    step(14, 21, 'Lean.Parser.Tactic.exact', 'exact f', [l], []),
    step(12, 21, 'Lean.cdot', '· exact f', [l, r], [r]),
    step(22, 29, 'Lean.Parser.Tactic.intro', 'intro h', [r], [r1]),
    step(30, 37, 'Lean.Parser.Tactic.exact', 'exact k', [r1], []),
    step(0, 37, 'Lean.Parser.Term.byTactic', 'by …', [g], []),
  ]);
  assert.deepEqual(proof.steps.map((s) => [s.kind, s.depth, s.kind === 'case' ? s.label : s.text]), [
    ['step', 0, 'constructor'], ['case', 0, '1'], ['step', 1, 'exact f'],
    ['case', 0, '2'], ['step', 1, 'intro h'], ['step', 1, 'exact k'],
  ]);
  const added = proof.steps[3];
  assert.equal(added.implied, true); // the proof has no marker here
  assert.deepEqual(added.results, [{ target: 'b → a', learned: [] }]);
  assert.equal(proof.steps[1].implied, undefined);
  assert.equal(proof.steps[5].within, '2');
});

test('rewrites one after the other on the same thing form a run, which the page can fold', () => {
  const g0 = goal('g0', 'A', [['h', 'p', true]]), g1 = goal('g1', 'B', [['h', 'p', true]]), g2 = goal('g2', 'C', [['h', 'p', true]]);
  const g3 = goal('g3', 'C', [['h', 'q', true]]), g4 = goal('g4', 'D', [['h', 'q', true]]);
  const proof = arrange([
    step(4, 5, 'null', 'a', [g0], [g1]), step(7, 8, 'null', 'b', [g1], [g2]), step(8, 9, '«]»', ']', [g2], [g2]),
    step(0, 9, 'Lean.Parser.Tactic.rwSeq', 'rw [a, b]', [g0], [g2]),
    step(14, 15, 'null', 'c', [g2], [g3]), step(15, 16, '«]»', ']', [g3], [g3]),
    step(10, 21, 'Lean.Parser.Tactic.rwSeq', 'rw [c] at h', [g2], [g3]),
    step(26, 27, 'null', 'd', [g3], [g4]), step(27, 28, '«]»', ']', [g4], [g4]),
    step(22, 28, 'Lean.Parser.Tactic.rwSeq', 'rw [d]', [g3], [g4]),
    step(29, 36, 'Lean.Parser.Tactic.exact', 'exact z', [g4], []),
  ]);
  // a and b rewrite the goal, c rewrites h, d the goal again: three runs; exact is in none
  assert.deepEqual(proof.steps.map((s) => [s.text, s.run]), [['a', 1], ['b', 1], ['c', 2], ['d', 3], ['exact z', undefined]]);
});

test('a piece of a longer command recorded without a name is not a rewrite: only what sits in the brackets of one is', () => {
  // `intro x y` is recorded as a whole and, without a name, as its first piece `intro x`
  const g = goal('g', '∀ x y, P x y', []), g1 = goal('g1', '∀ y, P x y', [['x', 'ℝ']]), g2 = goal('g2', 'P x y', [['x', 'ℝ'], ['y', 'ℝ']]);
  const proof = arrange([
    step(0, 7, 'null', 'intro x', [g], [g1]),
    step(8, 9, 'ident', 'y', [g1], [g2]), // and each further name on its own, as a term
    step(0, 9, 'Lean.Parser.Tactic.intro', 'intro x y', [g], [g2]),
    step(10, 17, 'Lean.Parser.Tactic.exact', 'exact h', [g2], []),
  ]);
  assert.deepEqual(proof.steps.map((s) => [s.text, s.rewrite, s.says]), [
    ['intro x y', false, 'take x, y arbitrary'], ['exact h', false, 'conclude with'],
  ]);
});

// ---------- each step said in plain words ----------
const said = (kind, text, before, after) => arrange([step(0, Buffer.byteLength(text), kind, text, before, after)]).steps[0].says;

test('in words: a split of an equivalence is "the two directions", read from the goals Lean recorded', () => {
  const iff = goal('g', 'a = b ↔ c = d'), l = goal('l', 'a = b → c = d'), r = goal('r', 'c = d → a = b');
  assert.equal(said('Lean.Parser.Tactic.constructor', 'constructor', [iff], [l, r]), 'prove the two directions separately');
  const and = goal('g', 'p ∧ q'), p = goal('p', 'p'), q = goal('q', 'q');
  assert.equal(said('Lean.Parser.Tactic.constructor', 'constructor', [and], [p, q]), 'prove the 2 parts separately');
});

test('in words: introducing says whether it is an object or an assumption', () => {
  const all = goal('g', '∀ n, P n', []), one = goal('g1', 'P n', [['n', 'ℕ']]);
  assert.equal(said('Lean.Parser.Tactic.intro', 'intro n', [all], [one]), 'take n arbitrary');
  const imp = goal('g', 'a → b', []), then = goal('g1', 'b', [['h', 'a', true]]);
  assert.equal(said('Lean.Parser.Tactic.intro', 'intro h', [imp], [then]), 'assume the premise, as h');
});

test('in words: taking a hypothesis apart names what it gives, or counts the cases', () => {
  const g = goal('g', 'Q', [['h', '∃ n, P n', true]]), got = goal('g1', 'Q', [['n', 'ℕ'], ['hn', 'P n', true]]);
  assert.equal(said('Lean.Parser.Tactic.rcases', 'rcases h with ⟨n, hn⟩', [g], [got]), 'from h, obtain n, hn');
  const or = goal('g', 'Q', [['h', 'a ∨ b', true]]);
  const l = goal('l', 'Q', [['h', 'a', true]]), r = goal('r', 'Q', [['h', 'b', true]]);
  assert.equal(said('Lean.Parser.Tactic.rcases', 'rcases h with h | h', [or], [l, r]), 'h is an "or": 2 cases');
});

test('in words: an "or" of two "there exists" taken apart says why there are cases and what each provides', () => {
  const g = goal('g', 'Q', [['H', '(∃ (n : ℤ), a n) ∨ ∃ (n : ℤ), b n', true]]);
  const l = goal('l', 'Q', [['n', 'ℤ'], ['hn', 'a n', true]]), r = goal('r', 'Q', [['n', 'ℤ'], ['hn', 'b n', true]]);
  assert.equal(said('Lean.Parser.Tactic.rcases', 'rcases H with (⟨n, hn⟩ | ⟨n, hn⟩)', [g], [l, r]), 'H is an "or": 2 cases; in each, it provides n, hn');
  // what is to prove is the same in every case: it is not repeated per case
  const proof = arrange([step(0, 30, 'Lean.Parser.Tactic.rcases', 'rcases H with (⟨n, hn⟩ | ⟨n, hn⟩)', [g], [l, r])]);
  assert.deepEqual(proof.steps[0].results.map((x) => x.target), [null, null]);
  // cases that are not from an "or" (here: a natural number is zero or a successor)
  const nat = goal('g', 'P k', [['k', 'ℕ']]), z = goal('z', 'P 0', []), s = goal('s', 'P (m + 1)', [['m', 'ℕ']]);
  assert.equal(said('Lean.Parser.Tactic.rcases', 'rcases k with _ | m', [nat], [z, s]), 'split k into 2 cases');
});

test('in words: automation says it is automatic, and where it works', () => {
  const g = goal('g', 'P', [['h', 'a', true]]), g1 = goal('g1', 'P', [['h', 'b', true]]);
  assert.equal(said('Lean.Parser.Tactic.simp', 'simp only [foo] at h', [g], [g1]), 'simplify h (automatic)');
  assert.equal(said('Mathlib.Tactic.linarith', 'linarith', [g], []), 'linear arithmetic from the hypotheses (automatic)');
  assert.equal(said('Lean.Parser.Tactic.simpa', 'simpa using h', [g], []), 'simplify, then conclude with the fact given (automatic)');
});

test('in words: common steps; a command not in the list, or a combination, is left as Lean wrote it', () => {
  const g = goal('g', 'P'), g1 = goal('g1', 'Q'), g2 = goal('g2', 'R');
  assert.equal(said('Lean.Parser.Tactic.exact', 'exact foo h', [g], []), 'conclude with');
  assert.equal(said('Lean.Parser.Tactic.apply', 'apply foo', [g], [g1]), 'it is enough to prove the premises of');
  assert.equal(said('Lean.Parser.Tactic.refine', 'refine ⟨_, ?_⟩', [g], [g1]), 'reduce to the gaps (?_) left in');
  assert.equal(said('Lean.Parser.Tactic.left', 'left', [g], [g1]), 'prove the left alternative');
  assert.equal(said('Lean.Parser.Tactic.induction', 'induction n with', [g], [g1, g2]), 'by induction on n');
  assert.equal(said('x', 'frobnicate h', [g], [g1]), null);
  // transitivity: a < c is proved as a < b and b < c
  assert.equal(said('Batteries.Tactic.tacticTrans___', 'trans y⁻¹', [goal('g', 'a < c')], [goal('p', 'a < y⁻¹'), goal('q', 'y⁻¹ < c')]), 'compare both sides with y⁻¹: 2 things to prove');
  assert.equal(said('Lean.Parser.Tactic.«tactic_<;>_»', 'constructor <;> simp', [g], []), null);
  const claim = goal('g1', 'P', [['x', 'ℝ'], ['h', '0 < x', true]]);
  assert.equal(said('Lean.Parser.Tactic.tacticHave__', 'have h : 0 < x := foo', [g], [claim]), 'intermediate claim h');
});

test('punctuation Lean records as a step of its own is not a step', () => {
  const g = goal('g', 'P'), g1 = goal('g1', 'Q');
  const proof = arrange([
    step(0, 4, 'Lean.Parser.Tactic.simp', 'simp', [g], [g1]),
    step(4, 5, '«;»', ';', [g1], [g1]),
    step(6, 13, 'Lean.Parser.Tactic.exact', 'exact h', [g1], []),
  ]);
  assert.deepEqual(proof.steps.map((s) => s.text), ['simp', 'exact h']);
});

test('in words: an assumption taken apart on the way in does not call what it gives "arbitrary"', () => {
  const g = goal('g', '(∃ k, a k) ∨ (∃ k, b k) → Q', []);
  const l = goal('l', 'Q', [['k', 'ℤ'], ['H', 'a k', true]]), r = goal('r', 'Q', [['k', 'ℤ'], ['H', 'b k', true]]);
  assert.equal(said('Lean.Parser.Tactic.rintro', 'rintro (⟨k, H⟩ | ⟨k, H⟩)', [g], [l, r]), 'assume the premise and split it into 2 cases');
  const one = goal('g', '(∃ k, a k) → Q', []);
  assert.equal(said('Lean.Parser.Tactic.rintro', 'rintro ⟨k, H⟩', [one], [l]), 'assume the premise; from it, obtain k, H');
});

// ---------- what a step cites ----------
const names = (start, stop, name) => ({ start, stop, kind: '@const', text: '', name, before: [], after: [] });

test('a step cites the declarations Lean resolved inside its own text; a rule used right to left says so', () => {
  const g0 = goal('g0', 'P', [['h', 'a = b', true]]), g1 = goal('g1', 'P', [['h', 'a - b = 0', true]]);
  const proof = arrange([
    names(6, 17, 'sub_eq_zero'),
    step(4, 17, 'null', '← sub_eq_zero', [g0], [g1]),
    step(17, 18, '«]»', ']', [g1], [g1]),
    step(0, 23, 'Lean.Parser.Tactic.rwSeq', 'rw [← sub_eq_zero] at h', [g0], [g1]),
  ]);
  assert.equal(proof.steps.length, 1); // what is cited is not a step
  assert.equal(proof.steps[0].text, 'sub_eq_zero');
  assert.equal(proof.steps[0].backwards, true);
  assert.deepEqual(proof.steps[0].cites, ['sub_eq_zero']);
});

test('a step that holds other steps cites only what its own line names, each once', () => {
  const g = goal('g', 'Q'), sub = goal('s', 'R'), g1 = goal('g1', 'Q', [['x', 'ℝ'], ['h', 'R', true]]);
  const proof = arrange([
    names(9, 12, 'Foo.bar'), names(13, 16, 'Foo.bar'),
    names(27, 30, 'baz'),
    step(21, 30, 'Lean.Parser.Tactic.exact', 'exact baz', [sub], []),
    step(0, 30, 'Lean.Parser.Tactic.tacticHave__', 'have h : bar bar := by\n  exact baz', [g], [g1]),
  ]);
  const have = proof.steps.find((s) => s.text.startsWith('have'));
  assert.deepEqual(have.cites, ['Foo.bar']);
  assert.equal(have.backwards, false);
  assert.deepEqual(proof.steps.find((s) => s.text === 'exact baz').cites, ['baz']);
});
