const { test } = require('node:test');
const assert = require('node:assert/strict');
const { expr, toLatex } = require('../public/lean-latex.js');

test('expr: symbols, application, square roots', () => {
  assert.equal(expr('Irrational (√2)'), '\\mathrm{Irrational}\\,\\left(\\sqrt{2}\\right)');
  assert.equal(expr('0 ≤ √x'), '0 \\le \\sqrt{x}');
  assert.equal(expr('Nat.Prime p'), '\\mathrm{Nat.Prime}\\,p');
  assert.equal(expr('mul_self_nonneg'), '\\mathrm{mul\\_self\\_nonneg}');
  assert.equal(expr('a * a = b * b ↔ a = b ∨ a = -b'), 'a^{2} = b^{2} \\iff a = b \\lor a = - b');
  assert.equal(expr('finrank K L ≤ #K'), '\\mathrm{finrank}\\,K\\,L \\le \\# K');
});

test('expr: powers bind to the whole application, as in Lean', () => {
  assert.equal(expr('(a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2'), '\\left(a - b\\right)^{2} = a^{2} - 2 \\cdot a \\cdot b + b^{2}');
  assert.equal(expr('f x ^ 2'), '\\left(f\\,x\\right)^{2}');
  assert.equal(expr('x ^ (n + 1)'), 'x^{n + 1}');
  assert.equal(expr('fun x => x⁻¹'), 'x \\mapsto x^{-1}');
  assert.equal(expr('x² + y₁'), 'x^{2} + y_{1}');
});

test('expr: binders, sets, big operators, number sets', () => {
  assert.equal(expr('∑ i ∈ s, f i'), '\\sum_{i \\in s} f\\,i');
  assert.equal(expr('{x | 0 < x}'), '\\{ x \\mid 0 < x \\}');
  assert.equal(expr('∀ ε > 0, ∃ δ > 0, ‖x‖ < δ'), '\\forall \\varepsilon > 0,\\; \\exists \\delta > 0,\\; \\| x \\| < \\delta');
  assert.equal(expr('x₁ ∈ Set.range ((↑) : ℚ → ℝ)'), 'x_{1} \\in \\mathrm{Set.range}\\,\\left(\\left(\\uparrow\\right) : \\mathbb{Q} \\to \\mathbb{R}\\right)');
  assert.equal(expr('(↑n : ℝ≥0∞) ≤ ⊤'), '\\left(n : \\overline{\\mathbb{R}}_{\\ge 0}\\right) \\le \\top');
  assert.equal(expr('α → Type*'), '\\alpha \\to \\mathrm{Type}');
});

test('expr: characters LaTeX treats specially are escaped', () => {
  assert.equal(expr('a % b'), 'a \\% b');
  assert.equal(expr('s \\ t'), 's \\setminus t');
  assert.equal(expr('foo_bar x'), '\\mathrm{foo\\_bar}\\,x');
});

test('toLatex: variables, hypotheses and conclusion', () => {
  const r = toLatex('theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p)', 'Nat.Prime.irrational_sqrt');
  assert.equal(r.kind, 'Theorem');
  assert.deepEqual(r.parts, [
    { text: 'Let ' }, { math: 'p \\in \\mathbb{N}' },
    { text: '. Assume ' }, { math: '\\mathrm{Nat.Prime}\\,p' }, { text: '. Then' },
    { math: '\\mathrm{Irrational}\\,\\left(\\sqrt{p}\\right)', display: true },
  ]);
  assert.equal(r.source,
    '\\begin{theorem}[\\texttt{Nat.Prime.irrational\\_sqrt}]\n' +
    'Let $p \\in \\mathbb{N}$. Assume $\\mathrm{Nat.Prime}\\,p$. Then\n' +
    '\\[ \\mathrm{Irrational}\\,\\left(\\sqrt{p}\\right) \\]\n' +
    '\\end{theorem}');
});

test('toLatex: a statement with no binders is just the conclusion', () => {
  const r = toLatex('/-- doc -/\ntheorem irrational_sqrt_two : Irrational (√2)', 'irrational_sqrt_two');
  assert.deepEqual(r.parts, [{ math: '\\mathrm{Irrational}\\,\\left(\\sqrt{2}\\right)', display: true }]);
});

test('toLatex: attributes, modifiers, instances, grouped names, default values', () => {
  const r = toLatex(
    '@[simp]\nprotected theorem mul_self_eq [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}\n    (h : Commute a b) (q : ℚ := 0) :\n    a * a = b * b ↔ a = b ∨ a = -b',
    'Commute.mul_self_eq'
  );
  assert.equal(
    r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''),
    'Let $R$ be a non-unital non-associative ring without zero divisors. Let $a, b \\in R$, $q \\in \\mathbb{Q}$. Assume $\\mathrm{Commute}\\,a\\,b$. Then'
  );
  assert.equal(r.parts.at(-1).display, true);
});

test('toLatex: a relation in a binder makes it a hypothesis whatever its name', () => {
  const r = toLatex('lemma foo (x : ℝ) (pos : 0 < x) (f : ℕ → ℝ) : 0 ≤ x', 'foo');
  assert.deepEqual(r.parts.slice(0, -1), [
    { text: 'Let ' }, { math: 'x \\in \\mathbb{R}' }, { text: ', ' }, { math: 'f : \\mathbb{N} \\to \\mathbb{R}' },
    { text: '. Assume ' }, { math: '0 < x' }, { text: '. Then' },
  ]);
});

test('toLatex: definitions show their type; structures and unparsable input give null', () => {
  const d = toLatex('noncomputable def sqrt (x : ℝ) : ℝ', 'Real.sqrt');
  assert.equal(d.kind, 'Definition');
  assert.deepEqual(d.parts, [
    { text: 'Let ' }, { math: 'x \\in \\mathbb{R}' }, { text: '. Then' },
    { math: '\\mathrm{Real.sqrt} : \\mathbb{R}', display: true },
  ]);
  assert.match(d.source, /^\\begin\{definition\}/);
  assert.equal(toLatex('structure Point (α : Type) where\n  x : α', 'Point'), null);
  assert.equal(toLatex('def Irrational (x : ℝ)', 'Irrational'), null); // no type to show
  assert.equal(toLatex('theorem broken (x : ℝ : 0 ≤ x', 'broken'), null);
  assert.equal(toLatex('', 'x'), null);
});

test('expr: preimage notation does not produce a double superscript', () => {
  assert.equal(expr("f ⁻¹' s ∈ l"), 'f^{-1}\\,s \\in l');
  assert.equal(expr("x' ⁻¹"), "x'^{-1}");
});

test('membership: a variable is "in" its type, unless that type is a function type or a universe', () => {
  const lets = (stmt) => toLatex(stmt, 'n').parts.filter((p) => p.math && !p.display).map((p) => p.math);
  assert.deepEqual(lets('theorem exists_rat_btwn {x y : K} (h : x < y) : ∃ q : ℚ, x < q ∧ q < y'), ['x, y \\in K', 'x < y']);
  assert.deepEqual(lets('theorem t {α : Type*} (s : Set α) (f : α → ℝ) (p : Prop) (F : ι → α → β) : True'), [
    '\\alpha', 's \\subseteq \\alpha', 'f : \\alpha \\to \\mathbb{R}', 'p : \\mathrm{Prop}',
    'F : \\iota \\to \\alpha \\to \\beta',
  ]);
});

test('membership inside quantifiers', () => {
  assert.equal(expr('∃ q : ℚ, x < q ∧ q < y'), '\\exists q \\in \\mathbb{Q},\\; x < q < y');
  assert.equal(expr('∀ (x : ℝ) (f : ℕ → ℝ), f 0 ≤ x'), '\\forall \\left(x \\in \\mathbb{R}\\right)\\,\\left(f : \\mathbb{N} \\to \\mathbb{R}\\right),\\; f\\,0 \\le x');
  assert.equal(expr('∀ ε > 0, (x : ℝ) ≤ ε'), '\\forall \\varepsilon > 0,\\; \\left(x : \\mathbb{R}\\right) \\le \\varepsilon'); // a type ascription keeps its colon
  assert.equal(expr('∀ α : Type*, Nonempty α'), '\\forall \\alpha : \\mathrm{Type},\\; \\mathrm{Nonempty}\\,\\alpha');
});

test('chains: `a < b ∧ b < c` is written a < b < c', () => {
  assert.equal(expr('∃ q : ℚ, x < q ∧ q < y'), '\\exists q \\in \\mathbb{Q},\\; x < q < y');
  assert.equal(expr('0 ≤ x ∧ x < 1'), '0 \\le x < 1');
  assert.equal(expr('a < b ∧ b ≤ c ∧ c = d'), 'a < b \\le c = d');
  assert.equal(expr('y > f x + 1 ∧ f x + 1 ≥ 0'), 'y > f\\,x + 1 \\ge 0');
  assert.equal(expr('(a < b ∧ b < c) → p'), '\\left(a < b < c\\right) \\to p');
  assert.equal(expr('a < b ∧ b < c ∨ d'), 'a < b < c \\lor d');
});

test('chains: not merged when that would change or blur the meaning', () => {
  assert.equal(expr('a < b ∧ c < d'), 'a < b \\land c < d'); // different middle terms
  assert.equal(expr('a < b ∧ b > c'), 'a < b \\land b > c'); // directions disagree
  assert.equal(expr('¬ a < b ∧ b < c'), '\\neg a < b \\land b < c'); // the negation covers only the first part
  assert.equal(expr('a ∈ s ∧ s ⊆ t'), 'a \\in s \\land s \\subseteq t'); // not order relations
  assert.equal(expr('a ≠ b ∧ b ≠ c'), 'a \\ne b \\land b \\ne c');
  assert.equal(expr('a < b ∧ b'), 'a < b \\land b');
});

test('a variable of type `Set α` is a subset of α', () => {
  const lets = (stmt) => toLatex(stmt, 'n').parts.filter((p) => p.math && !p.display).map((p) => p.math);
  assert.deepEqual(lets('theorem t (s t : Set α) (u : Set (α × β)) (v : Set.Icc a b) (F : Set α → Prop) : True'), [
    's, t \\subseteq \\alpha', 'u \\subseteq \\alpha \\times \\beta', 'v \\in \\mathrm{Set.Icc}\\,a\\,b', 'F : \\mathrm{Set}\\,\\alpha \\to \\mathrm{Prop}',
  ]);
  assert.equal(expr('∀ s : Set α, ∃ t : Set (Set α), s ∈ t'), '\\forall s \\subseteq \\alpha,\\; \\exists t \\subseteq \\mathrm{Set}\\,\\alpha,\\; s \\in t');
  assert.equal(expr('∀ (s : Set ℝ) (x : ℝ), x ∈ s'), '\\forall \\left(s \\subseteq \\mathbb{R}\\right)\\,\\left(x \\in \\mathbb{R}\\right),\\; x \\in s');
});

test('several hypotheses are joined as prose, without their Lean names', () => {
  const r = toLatex('theorem t (x y z : ℝ) (h₁ : x < y) (h₂ : y < z) (hz : z ≠ 0) : x < z', 't');
  assert.deepEqual(r.parts.slice(1, -1), [
    { math: 'x, y, z \\in \\mathbb{R}' }, { text: '. Assume ' }, { math: 'x < y' }, { text: ', ' }, { math: 'y < z' },
    { text: ' and ' }, { math: 'z \\ne 0' }, { text: '. Then' },
  ]);
  const two = toLatex('theorem t (h : a < b) (h\' : b < c) : a < c', 't');
  assert.deepEqual(two.parts.slice(0, -1), [{ text: 'Assume ' }, { math: 'a < b' }, { text: ' and ' }, { math: 'b < c' }, { text: '. Then' }]);
});

test('expr: the angle symbol', () => {
  assert.equal(expr('∠ p₁ p₂ p₃ = π / 2'), '\\angle p_{1}\\,p_{2}\\,p_{3} = \\pi / 2');
});

test('powers: a factor multiplied by itself is written as a power', () => {
  assert.equal(expr('dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂'),
    'd\\left(p_{1}, p_{3}\\right)^{2} = d\\left(p_{1}, p_{2}\\right)^{2} + d\\left(p_{3}, p_{2}\\right)^{2}');
  assert.equal(expr('x * x * x + 2 * y * y'), 'x^{3} + 2 \\cdot y^{2}');
  assert.equal(expr('(a + b) * (a + b)'), '\\left(a + b\\right)^{2}');
  assert.equal(expr('‖x‖ * ‖x‖'), '\\| x \\| \\cdot \\| x \\|'); // not a plain factor: left as written
});

test('powers: not merged when precedence would make it wrong', () => {
  assert.equal(expr('a / b * b'), 'a / b \\cdot b'); // (a / b) * b
  assert.equal(expr('b * b ^ 3'), 'b \\cdot b^{3}'); // b * (b ^ 3)
  assert.equal(expr('a ^ b * b'), 'a^{b} \\cdot b');
  assert.equal(expr('a * b'), 'a \\cdot b');
  assert.equal(expr('f a * f b'), 'f\\,a \\cdot f\\,b');
});

test('context: variables declared earlier in the file are introduced when the statement uses them', () => {
  const ctx = '{α : Type*} {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (unused : ℕ) [Fintype α]';
  const r = toLatex('theorem pyth (p₁ p₂ : P) : dist p₁ p₂ = dist p₂ p₁', 'pyth', ctx);
  assert.equal(
    r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''),
    'Let $V$ be a real inner product space, and let $P$ be a Euclidean affine space over $V$. Let $p_{1}, p_{2} \\in P$. Then'
  );
  // nothing from the context is used here
  assert.deepEqual(toLatex('theorem t : 1 = 1', 't', ctx).parts, [{ math: '1 = 1', display: true }]);
  // a hypothesis variable from the context that the statement mentions
  const h = toLatex('theorem t : 0 ≤ x', 't', '(x : ℝ) (hx : 0 < x) (y : ℝ)');
  assert.deepEqual(h.parts.slice(0, -1), [{ text: 'Let ' }, { math: 'x \\in \\mathbb{R}' }, { text: '. Then' }]);
});

test('context: only the names actually used are introduced, and the statement\'s own binders win', () => {
  const lets = (stmt, ctx) => toLatex(stmt, 'n', ctx).parts.filter((p) => p.math && !p.display).map((p) => p.math);
  assert.deepEqual(
    lets('theorem exists_rat_btwn {x y : K} (h : x < y) : ∃ q : ℚ, x < q ∧ q < y', '{G M R K : Type*} [Field K] [LinearOrder K] {x y ε : K}'),
    ['K', 'x, y \\in K', 'x < y'] // K is introduced once, as "a field and a linearly ordered set"
  );
  assert.deepEqual(lets('theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x', '{x y : ℝ}'), ['x \\in \\mathbb{R}']);
  assert.deepEqual(lets('theorem t : x ≤ y', '{x y z : ℝ}'), ['x, y \\in \\mathbb{R}']);
});

test('distance: d(x, y) in general, |AB| for points in Euclidean geometry', () => {
  assert.equal(expr('dist x y ≤ dist x z + dist z y'), 'd\\left(x, y\\right) \\le d\\left(x, z\\right) + d\\left(z, y\\right)');
  assert.equal(expr('dist (f x) y < ε'), 'd\\left(f\\,x, y\\right) < \\varepsilon');
  assert.equal(expr('Continuous dist'), '\\mathrm{Continuous}\\,\\mathrm{dist}'); // not applied to two points
  const geo = toLatex('theorem t (p₁ p₂ p₃ : P) : dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ ↔ dist (midpoint ℝ p₁ p₂) p₃ = 0', 'EuclideanGeometry.t');
  assert.equal(geo.parts.at(-1).math,
    '\\lvert p_{1} p_{3} \\rvert^{2} = \\lvert p_{1} p_{2} \\rvert^{2} \\iff d\\left(\\mathrm{midpoint}\\,\\mathbb{R}\\,p_{1}\\,p_{2}, p_{3}\\right) = 0');
  const general = toLatex('theorem t (x y : α) : dist x y = dist y x', 'dist_comm');
  assert.equal(general.parts.at(-1).math, 'd\\left(x, y\\right) = d\\left(y, x\\right)');
});

// The prose before the displayed formula, with formulas between dollars.
const prose = (stmt, ctx, name = 'n') => toLatex(stmt, name, ctx).parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join('');

test('phrasebook: typeclasses become sentences about their subject', () => {
  assert.equal(
    prose('theorem pyth (p₁ p₂ p₃ : P) : dist p₁ p₂ = dist p₂ p₃', '{V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]'),
    'Let $V$ be a real inner product space, and let $P$ be a Euclidean affine space over $V$. Let $p_{1}, p_{2}, p_{3} \\in P$. Then'
  );
  assert.equal(
    prose('theorem exists_rat_btwn {x y : K} (h : x < y) : ∃ q : ℚ, x < q ∧ q < y', '{G M R K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]'),
    'Let $K$ be an Archimedean linearly ordered field. Let $x, y \\in K$. Assume $x < y$. Then'
  );
  assert.equal(
    prose('theorem t [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) : a = b'),
    'Let $R$ be a non-unital non-associative ring without zero divisors. Let $a, b \\in R$. Assume $\\mathrm{Commute}\\,a\\,b$. Then'
  );
});

test('phrasebook: combinations, scalars, adjectives', () => {
  assert.equal(prose('theorem t {R M : Type*} [Field R] [AddCommGroup M] [Module R M] (x : M) : x = x'),
    'Let $R$ be a field, and let $M$ be a vector space over $R$. Let $x \\in M$. Then');
  assert.equal(prose('theorem t {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) : x = x'),
    'Let $R$ be a commutative ring, and let $M$ be a module over $R$. Let $x \\in M$. Then');
  assert.equal(prose('theorem t {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (x : E) : x = x'),
    'Let $E$ be a complex Banach space. Let $x \\in E$. Then');
  assert.equal(prose('theorem t {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X) : x = x'),
    'Let $X$ be a compact Hausdorff topological space. Let $x \\in X$. Then');
  assert.equal(prose('theorem t {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) : s = s'),
    'Let $\\alpha$ be a finite type. Let $s \\subseteq \\alpha$. Then');
  assert.equal(prose('theorem t {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (x : R) : x = x'),
    'Let $R$ be an integral domain of characteristic zero. Let $x \\in R$. Then');
  assert.equal(prose('theorem t {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [Algebra 𝕜 A] : (1 : A) = 1'),
    'Let $\\Bbbk$ be either $\\mathbb{R}$ or $\\mathbb{C}$, and let $A$ be an algebra over $\\Bbbk$. Then');
});

test('phrasebook: plain type variables, hypotheses in disguise, and unknown classes', () => {
  assert.equal(prose('theorem t {α β γ : Type*} (f : α → β) (g : β → γ) : g ∘ f = g ∘ f'),
    'Let $\\alpha$, $\\beta$ and $\\gamma$ be types. Let $f : \\alpha \\to \\beta$, $g : \\beta \\to \\gamma$. Then');
  assert.equal(prose('theorem t (n : ℕ) [NeZero n] [Fact (Nat.Prime n)] : n = n'),
    'Let $n \\in \\mathbb{N}$. Assume $n \\ne 0$ and $\\mathrm{Nat.Prime}\\,n$. Then');
  // not in the book: the Lean name is kept
  assert.equal(prose('theorem t {K : Type*} [Field K] [Frobnicable K] [Module K (K × K)] (x : K) : x = x'),
    'Let $K$ be a field. Let $x \\in K$, with $\\mathrm{Frobnicable}\\,K$, $\\mathrm{Module}\\,K\\,\\left(K \\times K\\right)$. Then');
  assert.equal(prose('theorem t [Frobnicable K] : (1 : K) = 1'), 'Given $\\mathrm{Frobnicable}\\,K$. Then');
});

test('a binder named like a fact (with an underscore) is a hypothesis', () => {
  assert.equal(prose('theorem t (f : α → ℝ) (f_mble : Measurable f) (x₀ : α) : f x₀ = f x₀'),
    'Let $f : \\alpha \\to \\mathbb{R}$, $x_{0} \\in \\alpha$. Assume $\\mathrm{Measurable}\\,f$. Then');
});

test('phrasebook: universe annotations on a class are ignored', () => {
  assert.equal(prose('theorem t {C : Type u} [Category.{v} C] (X : C) : X = X'), 'Let $C$ be a category. Let $X \\in C$. Then');
});
