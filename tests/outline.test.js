const { test } = require('node:test');
const assert = require('node:assert/strict');
const { outline } = require('../public/lean-outline.js');

const short = (steps) => steps.map((s) => [s.kind, s.depth, s.label || '', s.lean || s.text || s.count || ''].join(' | '));

test('a term proof has no outline', () => {
  assert.deepEqual(outline(':=\n  irrational_sqrt_natCast_iff.mpr hp.not_isSquare'), []);
  assert.deepEqual(outline(':= rfl'), []);
  assert.deepEqual(outline(''), []);
  assert.deepEqual(outline(undefined), []);
});

test('intermediate claims, with their names and the author\'s comments', () => {
  const body = [
    ':= by',
    '  -- First reduce to the case x ≠ 0.',
    '  -- This is harmless.',
    '  have hx : x ≠ 0 := by',
    '    intro h',
    '    simp [h] at hy',
    '  have h₂ : 0 < x ^ 2 := by positivity',
    '  obtain ⟨n, hn⟩ : ∃ n : ℕ, x < n := exists_nat_gt x',
    '  have := hn.le',
    '  exact foo hx h₂',
  ].join('\n');
  assert.deepEqual(short(outline(body)), [
    'note | 0 |  | First reduce to the case x ≠ 0. This is harmless.',
    'claim | 0 | hx | x ≠ 0',
    'tactics | 1 |  | 2',
    'claim | 0 | h₂ | 0 < x ^ 2',
    'obtain | 0 | n, hn | ∃ n : ℕ, x < n',
    'tactics | 0 |  | 2',
  ]);
});

test('a claim spread over several lines, and one with its own variables', () => {
  const body = [
    ':= by',
    '  have key (n : ℕ) (hn : 0 < n) :',
    '      f n ≤',
    '        g n := by',
    '    simp',
    '  have : ∀ ε > 0, ∃ δ > 0, ‖x‖ < δ :=',
    '    fun ε hε => ⟨ε, hε, h ε⟩',
  ].join('\n');
  const steps = outline(body);
  assert.deepEqual(steps.map((s) => [s.kind, s.label, s.binders, s.lean]), [
    ['claim', 'key', '(n : ℕ) (hn : 0 < n)', 'f n ≤ g n'],
    ['tactics', undefined, undefined, undefined],
    ['claim', 'this', '', '∀ ε > 0, ∃ δ > 0, ‖x‖ < δ'],
    ['tactics', undefined, undefined, undefined],
  ]);
});

test('suffices, show, case splits, local definitions, introductions, induction', () => {
  const body = [
    ':= by',
    '  intro x hx',
    '  suffices h : 0 ≤ x from le_of_lt h',
    '  show 0 ≤ x',
    '  by_cases hc : x = 0',
    '  · simp [hc]',
    '  · set y := x⁻¹ with hy',
    '    have hy0 : y ≠ 0 := inv_ne_zero hc',
    '    induction n with',
    '    | zero => simp',
    '    | succ k ih => exact ih',
  ].join('\n');
  assert.deepEqual(short(outline(body)), [
    'intro | 0 |  | x hx',
    'suffices | 0 | h | 0 ≤ x',
    'show | 0 |  | 0 ≤ x',
    'cases | 0 | hc | x = 0',
    'tactics | 1 |  | 1',
    'let | 1 |  | y := x⁻¹',
    'claim | 1 | hy0 | y ≠ 0',
    'induction | 1 |  | n',
    'tactics | 1 |  | 2',
  ]);
});

test('a calc block becomes one chain', () => {
  const body = [
    ':= by',
    '  calc a * b ≤ a * c := by gcongr',
    '    _ = c * a := mul_comm a c',
    '    _ < d := by',
    '      linarith',
  ].join('\n');
  assert.deepEqual(short(outline(body)), ['calc | 0 |  | a * b ≤ a * c = c * a < d']);
  const next = outline([':= by', '  calc', '    x = y := h', '    _ ≤ z := hz', '  done'].join('\n'));
  assert.deepEqual(short(next), ['calc | 0 |  | x = y ≤ z', 'tactics | 0 |  | 1']);
});

test('a claim without a statement is not a claim', () => {
  assert.deepEqual(short(outline(':= by\n  have := foo x\n  obtain ⟨y, hy⟩ := bar\n  exact baz')), ['tactics | 0 |  | 3']);
});

test('real proof: the engel lemma keeps its narrative and its claims in order', () => {
  const body = [
    ':= by',
    '  rcases E with ⟨_, x, hxU, rfl⟩',
    '  rintro ⟨_, y, hyU, rfl⟩',
    '  -- It will be useful to repackage the Engel subalgebras',
    '  set Ex : {engel K x | x ∈ U} := ⟨engel K x, x, hxU, rfl⟩',
    '  replace hUle : U ≤ Ex := hUle',
    '  -- We may and do assume that `x ≠ 0`, since otherwise the statement is trivial.',
    '  obtain rfl | hx₀ := eq_or_ne x 0',
    '  · simpa [Ex, Ey] using hmin Ey',
    '  have hr : 0 < r := by',
    '    apply Nat.pos_of_ne_zero',
  ].join('\n');
  assert.deepEqual(short(outline(body)), [
    'tactics | 0 |  | 2',
    'note | 0 |  | It will be useful to repackage the Engel subalgebras',
    'let | 0 |  | Ex := ⟨engel K x, x, hxU, rfl⟩',
    'claim | 0 | hUle | U ≤ Ex',
    'note | 0 |  | We may and do assume that `x ≠ 0`, since otherwise the statement is trivial.',
    'tactics | 0 |  | 1',
    'tactics | 1 |  | 1',
    'claim | 0 | hr | 0 < r',
    'tactics | 1 |  | 1',
  ]);
});

test('a local definition whose value starts on the next line names what is defined and its type', () => {
  const steps = outline(':= by\n  let E : LieSubmodule K U L :=\n  { engel K x with\n    lie_mem := sorry }\n  let F :=\n    foo\n  exact E');
  assert.deepEqual(steps.filter((s) => s.kind === 'let').map((s) => s.lean), ['E : LieSubmodule K U L', 'F']);
});
