const { test } = require('node:test');
const assert = require('node:assert/strict');
const { expr, toLatex } = require('../public/lean-latex.js');

test('expr: symbols, application, square roots', () => {
  assert.equal(expr('Irrational (√2)'), '\\sqrt{2} \\text{ is irrational}');
  assert.equal(expr('0 ≤ √x'), '0 \\le \\sqrt{x}');
  assert.equal(expr('Nat.Prime p'), 'p \\text{ is prime}');
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
  assert.equal(expr('(↑n : ℝ≥0∞) ≤ ⊤'), '\\iota_{\\overline{\\mathbb{R}}_{\\ge 0}}\\left(n\\right) \\le \\top');
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
    { text: '. Assume ' }, { math: 'p \\text{ is prime}' }, { text: '. Then' },
    { math: '\\sqrt{p} \\text{ is irrational}', display: true },
  ]);
  assert.equal(r.source,
    '\\begin{theorem}[\\texttt{Nat.Prime.irrational\\_sqrt}]\n' +
    'Let $p \\in \\mathbb{N}$. Assume $p \\text{ is prime}$. Then\n' +
    '\\[ \\sqrt{p} \\text{ is irrational} \\]\n' +
    '\\end{theorem}');
});

test('toLatex: a statement with no binders is just the conclusion', () => {
  const r = toLatex('/-- doc -/\ntheorem irrational_sqrt_two : Irrational (√2)', 'irrational_sqrt_two');
  assert.deepEqual(r.parts, [{ math: '\\sqrt{2} \\text{ is irrational}', display: true }]);
});

test('toLatex: attributes, modifiers, instances, grouped names, default values', () => {
  const r = toLatex(
    '@[simp]\nprotected theorem mul_self_eq [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}\n    (h : Commute a b) (q : ℚ := 0) :\n    a * a = b * b ↔ a = b ∨ a = -b',
    'Commute.mul_self_eq'
  );
  assert.equal(
    r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''),
    'Let $R$ be a non-unital non-associative ring without zero divisors. Let $a, b \\in R$, $q \\in \\mathbb{Q}$. Assume $a \\text{ and } b \\text{ commute}$. Then'
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
    { math: '\\sqrt{x} \\in \\mathbb{R}', display: true },
  ]);
  assert.match(d.source, /^\\begin\{definition\}/);
  assert.equal(toLatex('structure Point (α : Type) where\n  x : α', 'Point'), null);
  assert.equal(toLatex('def Irrational (x : ℝ)', 'Irrational'), null); // no type to show
  assert.equal(toLatex('theorem broken (x : ℝ : 0 ≤ x', 'broken'), null);
  assert.equal(toLatex('', 'x'), null);
});

test('expr: preimage notation does not produce a double superscript', () => {
  assert.equal(expr("f ⁻¹' s ∈ l"), 'f^{-1}\\left(s\\right) \\in l');
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
  assert.equal(expr('∀ (x : ℝ) (f : ℕ → ℝ), f 0 ≤ x'), '\\forall x \\in \\mathbb{R},\\; \\forall f : \\mathbb{N} \\to \\mathbb{R},\\; f\\,0 \\le x');
  assert.equal(expr('∀ ε > 0, (x : ℝ) ≤ ε'), '\\forall \\varepsilon > 0,\\; \\left(x : \\mathbb{R}\\right) \\le \\varepsilon'); // a type ascription keeps its colon
  assert.equal(expr('∀ α : Type*, Nonempty α'), '\\forall \\alpha : \\mathrm{Type},\\; \\alpha \\text{ is nonempty}');
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
    's, t \\subseteq \\alpha', 'u \\subseteq \\alpha \\times \\beta', 'v \\in \\left[a, b\\right]', 'F : \\mathcal{P}\\left(\\alpha\\right) \\to \\mathrm{Prop}',
  ]);
  assert.equal(expr('∀ s : Set α, ∃ t : Set (Set α), s ∈ t'), '\\forall s \\subseteq \\alpha,\\; \\exists t \\subseteq \\mathcal{P}\\left(\\alpha\\right),\\; s \\in t');
  assert.equal(expr('∀ (s : Set ℝ) (x : ℝ), x ∈ s'), '\\forall s \\subseteq \\mathbb{R},\\; \\forall x \\in \\mathbb{R},\\; x \\in s');
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
  assert.equal(expr('∠ p₁ p₂ p₃ = π / 2'), '\\angle p_{1} p_{2} p_{3} = \\frac{\\pi}{2}');
});

test('powers: a factor multiplied by itself is written as a power', () => {
  assert.equal(expr('dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂'),
    'd\\left(p_{1}, p_{3}\\right)^{2} = d\\left(p_{1}, p_{2}\\right)^{2} + d\\left(p_{3}, p_{2}\\right)^{2}');
  assert.equal(expr('x * x * x + 2 * y * y'), 'x^{3} + 2 \\cdot y^{2}');
  assert.equal(expr('(a + b) * (a + b)'), '\\left(a + b\\right)^{2}');
  assert.equal(expr('‖x‖ * ‖x‖'), '\\| x \\|^{2}');
});

test('powers: not merged when precedence would make it wrong', () => {
  assert.equal(expr('a / b * b'), '\\frac{a}{b} \\cdot b'); // (a / b) * b, not a / b²
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
  assert.equal(expr('Continuous dist'), '\\mathrm{dist} \\text{ is continuous}'); // not applied to two points
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
    'Let $R$ be a non-unital non-associative ring without zero divisors. Let $a, b \\in R$. Assume $a \\text{ and } b \\text{ commute}$. Then'
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
    'Let $n \\in \\mathbb{N}$. Assume $n \\ne 0$ and $n \\text{ is prime}$. Then');
  // not in the book: the Lean name is kept
  assert.equal(prose('theorem t {K : Type*} [Field K] [Frobnicable K] [Module K (K × K)] (x : K) : x = x'),
    'Let $K$ be a field. Let $x \\in K$, with $\\mathrm{Frobnicable}\\,K$, $\\mathrm{Module}\\,K\\,\\left(K \\times K\\right)$. Then');
  assert.equal(prose('theorem t [Frobnicable K] : (1 : K) = 1'), 'Given $\\mathrm{Frobnicable}\\,K$. Then');
});

test('a binder named like a fact (with an underscore) is a hypothesis', () => {
  assert.equal(prose('theorem t (f : α → ℝ) (f_mble : Measurable f) (x₀ : α) : f x₀ = f x₀'),
    'Let $f : \\alpha \\to \\mathbb{R}$, $x_{0} \\in \\alpha$. Assume $f \\text{ is measurable}$. Then');
});

test('phrasebook: universe annotations on a class are ignored', () => {
  assert.equal(prose('theorem t {C : Type u} [Category.{v} C] (X : C) : X = X'), 'Let $C$ be a category. Let $X \\in C$. Then');
});

test('angles: three named points are set tightly, anything else gets brackets', () => {
  assert.equal(expr('∠ A B C = π / 2'), '\\angle A B C = \\frac{\\pi}{2}');
  assert.equal(expr('∡ p₁ p₂ p₃ = 0'), '\\measuredangle p_{1} p_{2} p_{3} = 0');
  assert.equal(expr('∠ (midpoint ℝ a b) c d'), '\\angle\\left(\\mathrm{midpoint}\\,\\mathbb{R}\\,a\\,b, c, d\\right)');
  assert.equal(expr('angle x y = π / 3'), '\\angle\\left(x, y\\right) = \\frac{\\pi}{3}');
  assert.equal(expr('InnerProductGeometry.angle x (y - z) < π'), '\\angle\\left(x, y - z\\right) < \\pi');
  assert.equal(expr('Continuous angle'), '\\mathrm{angle} \\text{ is continuous}');
});

test('fractions: a division is typeset as a fraction when its two sides are clear', () => {
  assert.equal(expr('(a + b) / (c - d)'), '\\frac{a + b}{c - d}');
  assert.equal(expr('f x / y'), '\\frac{f\\,x}{y}');
  assert.equal(expr('x / f y + 1'), '\\frac{x}{f\\,y} + 1');
  assert.equal(expr('1 / 2 * x'), '\\frac{1}{2} \\cdot x');
  assert.equal(expr('a / b / c'), '\\frac{\\frac{a}{b}}{c}');
  assert.equal(expr('x ^ 2 / 2'), '\\frac{x^{2}}{2}');
  assert.equal(expr('- a / b'), '- \\frac{a}{b}');
  assert.equal(expr('a / b ^ 2'), 'a / b^{2}'); // the power belongs to b alone: left as written
  assert.equal(expr('a / -b'), 'a / - b');
});

test('the Pythagorean theorem, end to end', () => {
  const r = toLatex(
    'theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) :\n    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔\n      ∠ p₁ p₂ p₃ = π / 2',
    'EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two',
    '{V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]'
  );
  assert.equal(r.parts.at(-1).math,
    '\\lvert p_{1} p_{3} \\rvert^{2} = \\lvert p_{1} p_{2} \\rvert^{2} + \\lvert p_{3} p_{2} \\rvert^{2} \\iff \\angle p_{1} p_{2} p_{3} = \\frac{\\pi}{2}');
});

test('intervals are written as intervals', () => {
  assert.equal(expr('x ∈ Set.Icc a b'), 'x \\in \\left[a, b\\right]');
  assert.equal(expr('x ∈ Set.Ioo 0 (f y)'), 'x \\in \\left(0, f\\,y\\right)');
  assert.equal(expr('Ico a b ⊆ Ioc c d'), '\\left[a, b\\right) \\subseteq \\left(c, d\\right]');
  assert.equal(expr('Set.Ioi 0 ∪ Set.Iic a'), '\\left(0, +\\infty\\right) \\cup \\left(-\\infty, a\\right]');
  assert.equal(expr('Set.Ici a ∩ Set.Iio b'), '\\left[a, +\\infty\\right) \\cap \\left(-\\infty, b\\right)');
  assert.equal(expr('Continuous Set.Icc'), '\\mathrm{Set.Icc} \\text{ is continuous}'); // not applied to its bounds
});

test('French / Belgian notation: hat angles, outward brackets, slanted inequalities', () => {
  const fr = { notation: 'fr' };
  assert.equal(expr('∠ A B C = π / 2', fr), '\\widehat{A B C} = \\frac{\\pi}{2}');
  assert.equal(expr('∠ (midpoint ℝ a b) c d', fr), '\\angle\\left(\\mathrm{midpoint}\\,\\mathbb{R}\\,a\\,b, c, d\\right)');
  assert.equal(expr('x ∈ Set.Ioo a b', fr), 'x \\in \\left]a, b\\right[');
  assert.equal(expr('Ico a b ⊆ Ioc c d', fr), '\\left[a, b\\right[ \\subseteq \\left]c, d\\right]');
  assert.equal(expr('Set.Ioi 0 ∪ Set.Iic a', fr), '\\left]0, +\\infty\\right[ \\cup \\left]-\\infty, a\\right]');
  assert.equal(expr('x ∈ Set.Icc a b', fr), 'x \\in \\left[a, b\\right]');
  assert.equal(expr('0 ≤ x ∧ x < 1 ∨ y ≥ 2', fr), '0 \\leqslant x < 1 \\lor y \\geqslant 2');
  // the option does not leak into later calls
  assert.equal(expr('∠ A B C ≤ π'), '\\angle A B C \\le \\pi');
  const pyth = toLatex('theorem t (p₁ p₂ p₃ : P) : dist p₁ p₃ = 0 ↔ ∠ p₁ p₂ p₃ = π / 2', 'EuclideanGeometry.t', '', fr);
  assert.equal(pyth.parts.at(-1).math, '\\lvert p_{1} p_{3} \\rvert = 0 \\iff \\widehat{p_{1} p_{2} p_{3}} = \\frac{\\pi}{2}');
  assert.match(pyth.source, /widehat/);
  assert.doesNotMatch(toLatex('theorem t (p₁ p₂ p₃ : P) : ∠ p₁ p₂ p₃ = 0', 'EuclideanGeometry.t').source, /widehat/);
});

test('a declaration written with `lemma` is labelled a lemma', () => {
  const l = toLatex('lemma foo (x : ℝ) : 0 ≤ x ^ 2', 'foo');
  assert.equal(l.kind, 'Lemma');
  assert.match(l.source, /^\\begin\{lemma\}\[\\texttt\{foo\}\]\n[\s\S]*\\end\{lemma\}$/);
  assert.equal(l.parts.at(-1).math, '0 \\le x^{2}'); // the statement itself, not "foo : …"
  assert.equal(toLatex('theorem foo (x : ℝ) : 0 ≤ x ^ 2', 'foo').kind, 'Theorem');
  assert.equal(toLatex('protected lemma foo : 1 = 1', 'foo').kind, 'Lemma');
});

test('`variable (V)` only changes how V is passed: it does not introduce V again', () => {
  const ctx = '{α V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P] (V W)';
  assert.equal(prose('theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖', ctx),
    'Let $V$ be a seminormed abelian group, and let $P$ be a normed affine space over $V$. Let $x, y \\in P$. Then');
  // an untyped binder for a name nothing has introduced is still a variable
  assert.equal(prose('theorem t (x) (y : ℝ) : x = y'), 'Let $x$, $y \\in \\mathbb{R}$. Then');
});

test('expr: torsor subtraction and addition are written as plain − and +', () => {
  assert.equal(expr('dist x y = ‖x -ᵥ y‖'), 'd\\left(x, y\\right) = \\| x - y \\|');
  assert.equal(expr('v +ᵥ p = q'), 'v + p = q');
});

test('norms are one term: they pair up, nest, and take powers', () => {
  assert.equal(expr('‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2'),
    '\\| x - y \\|^{2} = \\| x \\|^{2} + \\| y \\|^{2} \\iff \\angle\\left(x, y\\right) = \\frac{\\pi}{2}');
  assert.equal(expr('‖f x‖ ≤ ‖f‖ * ‖x‖'), '\\| f\\,x \\| \\le \\| f \\| \\cdot \\| x \\|');
  assert.equal(expr('‖‖x‖ • y‖ = ‖x‖ * ‖y‖'), '\\| \\| x \\| \\bullet y \\| = \\| x \\| \\cdot \\| y \\|');
  assert.equal(expr('‖x‖ ^ 2 / ‖y‖'), '\\frac{\\| x \\|^{2}}{\\| y \\|}');
  assert.equal(expr('‖x‖₊ ≤ 1'), '\\| x \\| ₊ \\le 1'); // unknown decoration: kept, not lost
});

test('the statement is never restated: an angle of π/2 stays an angle, not "orthogonal"', () => {
  assert.equal(expr('angle x y = π / 2'), '\\angle\\left(x, y\\right) = \\frac{\\pi}{2}');
  assert.equal(expr('inner x y = 0 ↔ angle x y = π / 2'), '\\mathrm{inner}\\,x\\,y = 0 \\iff \\angle\\left(x, y\\right) = \\frac{\\pi}{2}');
  assert.doesNotMatch(expr('‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2'), /perp/);
});

test('inner products: double angle brackets, with the scalar field as a subscript', () => {
  assert.equal(expr('⟪x, y⟫_ℝ = 0'), '\\langle x, y \\rangle_{\\mathbb{R}} = 0');
  assert.equal(expr('⟪x - y, z⟫_𝕜'), '\\langle x - y, z \\rangle_{\\Bbbk}');
  assert.equal(expr('⟪x, y⟫ = ⟪y, x⟫'), '\\langle x, y \\rangle = \\langle y, x \\rangle');
  assert.equal(expr('⟪x, x⟫_ℝ = ‖x‖ * ‖x‖'), '\\langle x, x \\rangle_{\\mathbb{R}} = \\| x \\|^{2}');
  const r = toLatex('theorem t (x y : F) :\n    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0', 't', '{F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]');
  assert.equal(r.parts.at(-1).math, '\\| x - y \\|^{2} = \\| x \\|^{2} + \\| y \\|^{2} \\iff \\langle x, y \\rangle_{\\mathbb{R}} = 0');
});

test('thesis: the conclusion alone, for a node in the graph', () => {
  assert.equal(toLatex('theorem div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b', 'div_pos').thesis, '0 < \\frac{a}{b}');
  assert.equal(toLatex('lemma foo (x : ℝ) : 0 ≤ x ^ 2', 'foo').thesis, '0 \\le x^{2}');
  assert.equal(toLatex('theorem t : ∠ A B C = π / 2', 'EuclideanGeometry.t', '', { notation: 'fr' }).thesis, '\\widehat{A B C} = \\frac{\\pi}{2}');
});

test('expr: script capitals such as the neighbourhood filter 𝓝', () => {
  assert.equal(expr('Tendsto f l (𝓝 a)'), 'f \\text{ tends to } a \\text{ along } l');
  assert.equal(expr('s ∈ 𝓤 α'), 's \\in \\mathcal{U}\\,\\alpha');
  assert.equal(expr('𝓝[s] a'), '\\mathcal{N}\\,\\left[s\\right]\\,a');
});

test('a variable of type ℝ≥0 is a variable, not a hypothesis', () => {
  assert.equal(prose('theorem coe_nonneg (r : ℝ≥0) (x : ℝ≥0∞) : (0 : ℝ) ≤ r'),
    'Let $r \\in \\mathbb{R}_{\\ge 0}$, $x \\in \\overline{\\mathbb{R}}_{\\ge 0}$. Then');
});


test('definitions: the thesis is the signature, what the thing is, not how it is computed', () => {
  const thesis = (stmt, name = 'n', ctx) => toLatex(stmt, name, ctx).thesis;
  assert.equal(thesis('noncomputable def arg (x : ℂ) : ℝ', 'Complex.arg'), '\\arg : \\mathbb{C} \\to \\mathbb{R}');
  assert.equal(thesis('def angle (x y : V) : ℝ', 'InnerProductGeometry.angle'), '\\mathrm{angle} : V \\times V \\to \\mathbb{R}');
  assert.equal(thesis('def image {α β : Type*} (f : α → β) (s : Set α) : Set β', 'Set.image'),
    '\\mathrm{image} : \\left(\\alpha \\to \\beta\\right) \\times \\mathcal{P}\\left(\\alpha\\right) \\to \\mathcal{P}\\left(\\beta\\right)');
  assert.equal(thesis('def Prime (p : ℕ) : Prop', 'Nat.Prime'), '\\mathrm{Prime} : \\mathbb{N} \\to \\mathrm{Prop}');
  assert.equal(thesis('noncomputable def pi : ℝ', 'Real.pi'), '\\pi \\in \\mathbb{R}');
  // a later argument whose type mentions an earlier one cannot be written as a product
  assert.equal(thesis('def get (l : List α) (i : Fin l.length) : α', 'List.get'), '\\mathrm{get}\\,l\\,i \\in \\alpha');
  assert.equal(toLatex('def Irrational (x : ℝ)', 'Irrational'), null); // no stated type: nothing to show
});

test('definitions: focused, the statement introduces the arguments and gives the result type', () => {
  const r = toLatex('noncomputable def arg (x : ℂ) : ℝ', 'Complex.arg');
  assert.equal(r.kind, 'Definition');
  assert.equal(r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''), 'Let $x \\in \\mathbb{C}$. Then');
  assert.equal(r.parts.at(-1).math, '\\arg\\,x \\in \\mathbb{R}');
});

test('expr: a projection applies to the bracket just before it', () => {
  assert.equal(expr('(-x).fst / ‖x‖'), '\\frac{\\left(- x\\right).\\mathrm{fst}}{\\| x \\|}');
  assert.equal(expr('Real.arcsin ((-x).im / ‖x‖) + π'), '\\arcsin\\,\\left(\\frac{\\operatorname{Im}\\left(- x\\right)}{\\| x \\|}\\right) + \\pi');
  assert.equal(expr('(f x).1 ≤ (f x).2'), '\\left(f\\,x\\right).1 \\le \\left(f\\,x\\right).2');
  assert.equal(expr('(a + b).foo_bar c'), '\\left(a + b\\right).\\mathrm{foo\\_bar}\\,c');
});

test('standard symbols: constants and elementary functions get their usual sign', () => {
  assert.equal(expr('Real.pi'), '\\pi');
  assert.equal(expr('2 * pi * r'), '2 \\cdot \\pi \\cdot r');
  assert.equal(expr('Complex.exp (Complex.I * Real.pi) = -1'), '\\exp\\,\\left(i \\cdot \\pi\\right) = - 1');
  assert.equal(expr('Real.sin x ^ 2 + Real.cos x ^ 2 = 1'), '\\left(\\sin\\,x\\right)^{2} + \\left(\\cos\\,x\\right)^{2} = 1');
  assert.equal(expr('Real.log (x * y) = Real.log x + Real.log y'), '\\log\\,\\left(x \\cdot y\\right) = \\log\\,x + \\log\\,y');
  assert.equal(expr('arcsin x + Real.arccos x = π / 2'), '\\arcsin\\,x + \\arccos\\,x = \\frac{\\pi}{2}');
  assert.equal(expr('Real.arsinh (sinh x) = x'), '\\operatorname{arsinh}\\,\\left(\\sinh\\,x\\right) = x');
  assert.equal(expr('Real.goldenRatio ^ 2 = Real.goldenRatio + 1'), '\\varphi^{2} = \\varphi + 1');
});

test('standard symbols: square root, absolute value, factorial, binomial, gcd, real and imaginary parts', () => {
  assert.equal(expr('Real.sqrt (x ^ 2) = abs x'), '\\sqrt{x^{2}} = \\lvert x \\rvert');
  assert.equal(expr('NNReal.sqrt x ≤ sqrt y'), '\\sqrt{x} \\le \\sqrt{y}');
  assert.equal(expr('Nat.factorial (n + 1) = (n + 1) * Nat.factorial n'), '\\left(n + 1\\right)! = \\left(n + 1\\right) \\cdot n!');
  assert.equal(expr('Nat.choose n k = Nat.choose n (n - k)'), '\\binom{n}{k} = \\binom{n}{n - k}');
  assert.equal(expr('Nat.gcd a b ∣ Nat.lcm a b'), '\\gcd\\left(a, b\\right) \\mid \\operatorname{lcm}\\left(a, b\\right)');
  assert.equal(expr('max a b = max b a'), '\\max\\left(a, b\\right) = \\max\\left(b, a\\right)');
  assert.equal(expr('z.re ^ 2 + z.im ^ 2'), '\\operatorname{Re}\\left(z\\right)^{2} + \\operatorname{Im}\\left(z\\right)^{2}');
  assert.equal(expr('(-x).im / ‖x‖'), '\\frac{\\operatorname{Im}\\left(- x\\right)}{\\| x \\|}');
});

test('standard symbols: only the standard meaning is replaced', () => {
  assert.equal(expr('Finset.pi s t'), '\\mathrm{Finset.pi}\\,s\\,t'); // a different pi
  assert.equal(expr('Filter.exp f'), '\\mathrm{Filter.exp}\\,f');
  assert.equal(expr('Continuous Real.sqrt'), '\\sqrt{\\cdot} : \\mathbb{R} \\to \\mathbb{R} \\text{ is continuous}'); // not applied to anything
  assert.equal(expr('Continuous Real.exp'), '\\exp : \\mathbb{R} \\to \\mathbb{R} \\text{ is continuous}');
  assert.equal(expr('p.re'), '\\operatorname{Re}\\left(p\\right)');
  assert.equal(expr('Foo.bar.re'), '\\mathrm{Foo.bar.re}'); // not a variable's real part
});

test('standard symbols in a definition\'s signature', () => {
  assert.equal(toLatex('noncomputable def pi : ℝ', 'Real.pi').thesis, '\\pi \\in \\mathbb{R}');
  assert.equal(toLatex('noncomputable def arg (x : ℂ) : ℝ', 'Complex.arg').thesis, '\\arg : \\mathbb{C} \\to \\mathbb{R}');
  assert.equal(toLatex('noncomputable def sqrt (x : ℝ) : ℝ', 'Real.sqrt').thesis, '\\sqrt{\\cdot} : \\mathbb{R} \\to \\mathbb{R}');
  assert.equal(toLatex('def exp (x : ℂ) : ℂ', 'Complex.exp').parts.at(-1).math, '\\exp\\,x \\in \\mathbb{C}');
});

test('standard symbols: a bare I is the imaginary unit only in a statement about complex numbers', () => {
  assert.equal(toLatex('theorem exp_pi_mul_I : exp (π * I) = -1', 'Complex.exp_pi_mul_I').thesis, '\\exp\\,\\left(\\pi \\cdot i\\right) = - 1');
  assert.equal(toLatex('theorem mem (I : Ideal R) (x : R) : x ∈ I', 'Ideal.mem').thesis, 'x \\in I');
  assert.equal(expr('x ∈ I'), 'x \\in I');
});

test('abbreviations: a shorthand is shown as what it stands for', () => {
  const abbrev = (stmt, body, name = 'n', ctx) => toLatex(stmt, name, ctx, { body });
  const r = abbrev('abbrev ConstructibleSetData', ':= Finset (BasicConstructibleSetData R)', 'PrimeSpectrum.ConstructibleSetData');
  assert.equal(r.kind, 'Abbreviation');
  assert.equal(r.thesis, '\\mathrm{ConstructibleSetData} := \\mathcal{P}_{\\mathrm{fin}}\\left(\\mathrm{BasicConstructibleSetData}\\,R\\right)');
  assert.equal(r.parts.at(-1).math, r.thesis);
  const withArgs = abbrev('abbrev Short {α : Type*} (x : α) : α', ':= Hub x');
  assert.equal(withArgs.thesis, '\\mathrm{Short}\\,x := \\mathrm{Hub}\\,x');
  assert.equal(withArgs.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''), 'Let $\\alpha$ be a type. Let $x \\in \\alpha$. Write');
});

test('abbreviations: when the body is a program, or missing, the signature is shown as for a definition', () => {
  const thesis = (body) => (toLatex('abbrev f (n : ℕ) : ℕ', 'f', '', { body }) || {}).thesis;
  for (const body of [':= by\n  exact n', 'where\n  toFun := id', ':= { toFun := id }', ':= ⟨n, rfl⟩', ':=\n  let m := n + 1\n  m', ':= ' + 'n + '.repeat(120) + 'n', undefined]) {
    assert.equal(thesis(body), 'f : \\mathbb{N} \\to \\mathbb{N}');
  }
  assert.equal(toLatex('abbrev T', 'T', '', { body: ':= by exact ℕ' }), null); // neither a formula nor a type
  // a definition's or a theorem's body is never taken for its formula
  assert.equal(toLatex('def f (n : ℕ) : ℕ', 'f', '', { body: ':= n + 1' }).thesis, 'f : \\mathbb{N} \\to \\mathbb{N}');
  assert.equal(toLatex('theorem t : 1 = 1', 't', '', { body: ':= rfl' }).thesis, '1 = 1');
});

test('generated projections: worded from their name', () => {
  const { projection } = require('../public/lean-phrases.js');
  assert.deepEqual(projection('Semiring.toNonAssocSemiring', 'NonAssocSemiring'), { words: 'every semiring is a non-associative semiring' });
  assert.deepEqual(projection('CategoryTheory.Category.toCategoryStruct', 'CategoryTheory.CategoryStruct'), { words: 'every `Category` is a `CategoryStruct`' });
  assert.deepEqual(projection('Norm.norm', null), { tex: '\\| x \\|', words: 'norm' });
  assert.deepEqual(projection('Dist.dist', null), { tex: 'd(x, y)', words: 'distance' });
  assert.deepEqual(projection('CategoryTheory.Functor.obj', null), { words: '`obj` of a `Functor`' });
  assert.deepEqual(projection('Units.val', null), { words: '`val` of a `Units`' });
  assert.equal(projection('pi', null), null); // no owner to speak of
});

test('image and preimage of a set: f(S) and f⁻¹(S)', () => {
  assert.equal(expr("0 ∈ cos '' Icc (1 : ℝ) 2"), '0 \\in \\cos\\left(\\left[1 : \\mathbb{R}, 2\\right]\\right)');
  assert.equal(expr("f '' s ⊆ t"), 'f\\left(s\\right) \\subseteq t');
  assert.equal(expr("f '' (s ∪ t) = f '' s ∪ f '' t"), 'f\\left(s \\cup t\\right) = f\\left(s\\right) \\cup f\\left(t\\right)');
  assert.equal(expr("(fun x => x + 1) '' s"), '\\left(x \\mapsto x + 1\\right)\\left(s\\right)');
  assert.equal(expr("g ∘ f '' s"), 'g \\circ f\\left(s\\right)');
  assert.equal(expr("f ⁻¹' (t ∩ u)"), 'f^{-1}\\left(t \\cap u\\right)');
  assert.equal(expr("x'' + y'"), "x'' + y'"); // primes on a name are not the image sign
  const r = toLatex("theorem exists_cos_eq_zero : 0 ∈ cos '' Icc (1 : ℝ) 2", 'Real.exists_cos_eq_zero');
  assert.equal(r.thesis, '0 \\in \\cos\\left(\\left[1 : \\mathbb{R}, 2\\right]\\right)');
});

test('towers of powers and repeated superscripts stay valid', () => {
  assert.equal(expr('x ^ p ^ n = 0'), 'x^{p^{n}} = 0'); // Lean reads x ^ (p ^ n)
  assert.equal(expr('a ^ b ^ c ^ d'), 'a^{b^{c^{d}}}');
  assert.equal(expr('(c - 1)⁻¹ ^ 3'), '\\left(\\left(c - 1\\right)^{-1}\\right)^{3}');
  assert.equal(expr('x² ^ n'), '\\left(x^{2}\\right)^{n}');
  assert.equal(expr('x ^ 2 * y ^ 2'), 'x^{2} \\cdot y^{2}');
});

test('indexed infimum and supremum use signs the typesetter knows', () => {
  assert.equal(expr('⨅ i, f i'), '\\mathop{\\sqcap}_{i} f\\,i');
  assert.equal(expr('⨆ i, f i'), '\\bigsqcup_{i} f\\,i');
});

test('predicates are worded: a property of a function', () => {
  assert.equal(expr('ContinuousOn f s'), 'f \\text{ is continuous on } s');
  assert.equal(expr('StrictConcaveOn ℝ s f'), 'f \\text{ is strictly concave on } s');
  assert.equal(expr('Continuous f ∧ Function.Injective g'), 'f \\text{ is continuous} \\land g \\text{ is injective}');
  assert.equal(expr('DifferentiableAt ℝ f x'), 'f \\text{ is differentiable at } x');
  assert.equal(expr("HasDerivAt f f' x"), "f \\text{ has derivative } f' \\text{ at } x");
  assert.equal(expr('StrictMono f → Monotone f'), 'f \\text{ is strictly increasing} \\to f \\text{ is monotone}');
  assert.equal(expr('Continuous (fun x => f x + g x)'), '\\left(x \\mapsto f\\,x + g\\,x\\right) \\text{ is continuous}');
  assert.equal(expr('ContDiff ℝ n f'), 'f \\text{ is of class } C^{n}');
  assert.equal(expr('Set.MapsTo f s t'), 'f \\text{ maps } s \\text{ into } t');
});

test('predicates are worded: sets, numbers, pairs', () => {
  assert.equal(expr('IsCompact s → IsClosed s'), 's \\text{ is compact} \\to s \\text{ is closed}');
  assert.equal(expr('Irrational (√2)'), '\\sqrt{2} \\text{ is irrational}');
  assert.equal(expr('Nat.Prime p ∧ Odd p'), 'p \\text{ is prime} \\land p \\text{ is odd}');
  assert.equal(expr('Disjoint s t'), 's \\text{ and } t \\text{ are disjoint}');
  assert.equal(expr('IsCoprime a b'), 'a \\text{ and } b \\text{ are coprime}');
  assert.equal(expr('IsLeast s a'), 'a \\text{ is the least element of } s');
  assert.equal(expr('Convex ℝ s'), 's \\text{ is convex}');
  assert.equal(expr('Integrable f μ'), 'f \\text{ is integrable}');
  assert.equal(expr('Integrable f'), 'f \\text{ is integrable}');
  assert.equal(expr('IsIntegral R x'), 'x \\text{ is integral over } R');
});

test('predicates written with a dot after their subject', () => {
  assert.equal(expr('s.Nonempty'), 's \\text{ is nonempty}');
  assert.equal(expr('p.Prime → 2 ≤ p'), 'p \\text{ is prime} \\to 2 \\le p');
  assert.equal(expr('f.Injective'), 'f \\text{ is injective}');
  assert.equal(expr('s.Finite ∧ t.Infinite'), 's \\text{ is finite} \\land t \\text{ is infinite}');
  assert.equal(expr('Foo.bar.Nonempty'), '\\mathrm{Foo.bar.Nonempty}'); // not a variable
});

test('limits: Tendsto is written as a limit', () => {
  assert.equal(expr('Tendsto f atTop (𝓝 a)'), 'f \\text{ tends to } a \\text{ at } +\\infty');
  assert.equal(expr('Tendsto f (𝓝 x) (𝓝 (f x))'), 'f \\text{ tends to } f\\,x \\text{ at } x');
  assert.equal(expr('Tendsto f atBot atTop'), 'f \\text{ tends to } +\\infty \\text{ at } -\\infty');
  assert.equal(expr('Tendsto f l m'), 'f \\text{ tends to } m \\text{ along } l');
});

test('predicates: left alone when not applied as expected', () => {
  assert.equal(expr('Continuous'), '\\mathrm{Continuous}');
  assert.equal(expr('ContinuousOn f'), '\\mathrm{ContinuousOn}\\,f'); // an argument is missing
  assert.equal(expr('Foo.Continuous f'), '\\mathrm{Foo.Continuous}\\,f'); // some other Continuous
  assert.equal(expr('MyPredicate f s'), '\\mathrm{MyPredicate}\\,f\\,s');
});

test('predicates in a whole statement', () => {
  assert.equal(prose('theorem t (f : ℝ → ℝ) (hf : Continuous f) (s : Set ℝ) (hs : IsCompact s) : BddAbove (f \'\' s)'),
    'Let $f : \\mathbb{R} \\to \\mathbb{R}$, $s \\subseteq \\mathbb{R}$. Assume $f \\text{ is continuous}$ and $s \\text{ is compact}$. Then');
  assert.equal(toLatex("theorem t (f : ℝ → ℝ) (s : Set ℝ) : BddAbove (f '' s)", 't').thesis, 'f\\left(s\\right) \\text{ is bounded above}');
});

test('an interval may have a symbol such as π or ∞ as a bound', () => {
  assert.equal(expr('Icc 0 π'), '\\left[0, \\pi\\right]');
  assert.equal(expr('Set.InjOn cos (Icc 0 π)'), '\\cos \\text{ is injective on } \\left[0, \\pi\\right]');
  assert.equal(expr('Set.Ioo (-π) π'), '\\left(- \\pi, \\pi\\right)');
});

test('a root and what it covers are one term, as Lean prints them without brackets', () => {
  assert.equal(expr('Irrational √2'), '\\sqrt{2} \\text{ is irrational}');
  assert.equal(expr('√x * √x = x'), '\\sqrt{x}^{2} = x');
  assert.equal(expr('1 / √(x + 1)'), '\\frac{1}{\\sqrt{x + 1}}');
  assert.equal(expr('Real.sqrt_nonneg √'), '\\mathrm{Real.sqrt\\_nonneg}\\,\\sqrt{{}}'); // a root sign with nothing after it
});

test('statements as Lean prints them: full names, instances called self, universe names', () => {
  assert.equal(prose('theorem continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s', '', 'Real.continuousOn_cos'), 'Let $s \\subseteq \\mathbb{R}$. Then');
  assert.equal(toLatex('theorem continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s', 'Real.continuousOn_cos', '').thesis, '\\cos : \\mathbb{R} \\to \\mathbb{R} \\text{ is continuous on } s');
  assert.equal(toLatex('abbrev toNonAssocSemiring {α : Type u} [self : Semiring α] : NonAssocSemiring α', 'Semiring.toNonAssocSemiring', '').thesis,
    '\\mathrm{toNonAssocSemiring} \\in \\mathrm{NonAssocSemiring}\\,\\alpha');
});

test('notation as Lean prints it: rexp, cexp and the postfix factorial', () => {
  assert.equal(expr('Filter.Tendsto rexp Filter.atTop Filter.atTop'), '\\exp : \\mathbb{R} \\to \\mathbb{R} \\text{ tends to } +\\infty \\text{ at } +\\infty');
  assert.equal(expr('cexp (π * I)'), '\\exp\\,\\left(\\pi \\cdot I\\right)');
  assert.equal(expr('(n + 1)! = (n + 1) * n !'), '\\left(n + 1\\right)! = \\left(n + 1\\right) \\cdot n!');
  assert.equal(expr('n ! ∣ m !'), 'n! \\mid m!');
  assert.equal(expr('0 ≤ ↑r'), '0 \\le \\iota\\left(r\\right)');
});

test('a standard function named as the subject of a property carries its domain and range', () => {
  assert.equal(expr('Continuous Real.cos'), '\\cos : \\mathbb{R} \\to \\mathbb{R} \\text{ is continuous}');
  assert.equal(expr('Differentiable ℂ Complex.exp'), '\\exp : \\mathbb{C} \\to \\mathbb{C} \\text{ is differentiable}');
  assert.equal(expr('StrictMonoOn Real.arcsin (Set.Icc (-1) 1)'), '\\arcsin : \\mathbb{R} \\to \\mathbb{R} \\text{ is strictly increasing on } \\left[- 1, 1\\right]');
  assert.equal(expr('Continuous Complex.arg'), '\\arg : \\mathbb{C} \\to \\mathbb{R} \\text{ is continuous}');
  assert.equal(expr('Continuous NNReal.sqrt'), '\\sqrt{\\cdot} : \\mathbb{R}_{\\ge 0} \\to \\mathbb{R}_{\\ge 0} \\text{ is continuous}');
  assert.equal(expr('Continuous rexp ∧ Continuous cexp'), '\\exp : \\mathbb{R} \\to \\mathbb{R} \\text{ is continuous} \\land \\exp : \\mathbb{C} \\to \\mathbb{C} \\text{ is continuous}');
});

test('the domain is only added where it is known and useful', () => {
  assert.equal(expr('Continuous cos'), '\\cos \\text{ is continuous}'); // which cosine is not said
  assert.equal(expr('Real.cos x ≤ 1'), '\\cos\\,x \\le 1'); // applied: x says it
  assert.equal(expr('Continuous (fun x => Real.cos x)'), '\\left(x \\mapsto \\cos\\,x\\right) \\text{ is continuous}');
  assert.equal(expr('Continuous Nat.gcd'), '\\gcd \\text{ is continuous}'); // not a function of one variable
  // inside the Real namespace the source writes a bare `cos`
  assert.equal(toLatex('theorem continuous_cos : Continuous cos', 'Real.continuous_cos').thesis, '\\cos : \\mathbb{R} \\to \\mathbb{R} \\text{ is continuous}');
  assert.equal(toLatex('theorem continuous_cos : Continuous cos', 'Complex.continuous_cos').thesis, '\\cos : \\mathbb{C} \\to \\mathbb{C} \\text{ is continuous}');
  assert.equal(toLatex('theorem t : Continuous cos', 'Foo.t').thesis, '\\cos \\text{ is continuous}');
});

test('limits are said in words, name the function with its domain, and know one-sided limits', () => {
  assert.equal(expr('Filter.Tendsto Real.cos (𝓝[<] (π / 2)) (𝓝[>] 0)'),
    '\\cos : \\mathbb{R} \\to \\mathbb{R} \\text{ tends to } 0^{+} \\text{ at } \\left(\\frac{\\pi}{2}\\right)^{-}');
  assert.equal(expr('Tendsto f (𝓝[>] a) atTop'), 'f \\text{ tends to } +\\infty \\text{ at } a^{+}');
  assert.equal(expr('Tendsto f (𝓝[≠] a) (𝓝 b)'), 'f \\text{ tends to } b \\text{ at } a \\text{ (excluded)}');
  assert.equal(expr('Tendsto f (𝓝[s] a) (𝓝 b)'), 'f \\text{ tends to } b \\text{ at } a \\text{ within } s');
  assert.equal(expr('Tendsto f (𝓝[Set.Ici a] a) (𝓝 b)'), 'f \\text{ tends to } b \\text{ at } a \\text{ within } \\left[a, +\\infty\\right)');
  assert.equal(expr('Tendsto Real.log atTop atTop'), '\\log : \\mathbb{R} \\to \\mathbb{R} \\text{ tends to } +\\infty \\text{ at } +\\infty');
  assert.equal(expr('Tendsto (fun r => r⁻¹) atTop (𝓝 0)'), '\\left(r \\mapsto r^{-1}\\right) \\text{ tends to } 0 \\text{ at } +\\infty');
});


test('coercions: a cast is written as a named map ι, introduced in words', () => {
  const r = toLatex('theorem ofReal_div (r s : ℝ) : (↑(r / s) : ℂ) = (↑r : ℂ) / (↑s : ℂ)', 'Complex.ofReal_div', '');
  assert.equal(r.thesis, '\\iota\\left(\\frac{r}{s}\\right) = \\frac{\\iota\\left(r\\right)}{\\iota\\left(s\\right)}');
  assert.equal(r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''),
    'Let $r, s \\in \\mathbb{R}$. Let $\\iota : \\mathbb{R} \\to \\mathbb{C}$ be the canonical map. Then');
  assert.equal(r.source,
    '\\begin{theorem}[\\texttt{Complex.ofReal\\_div}]\n' +
    'Let $r, s \\in \\mathbb{R}$. Let $\\iota : \\mathbb{R} \\to \\mathbb{C}$ be the canonical map. Then\n' +
    '\\[ \\iota\\left(\\frac{r}{s}\\right) = \\frac{\\iota\\left(r\\right)}{\\iota\\left(s\\right)} \\]\n' +
    '\\end{theorem}');
  assert.equal(prose('theorem coe_nonneg (r : ℝ≥0) : 0 ≤ (↑r : ℝ)'),
    'Let $r \\in \\mathbb{R}_{\\ge 0}$. Let $\\iota : \\mathbb{R}_{\\ge 0} \\to \\mathbb{R}$ be the canonical map. Then');
});

test('coercions: when where the map starts is not written, only where it lands is said', () => {
  assert.equal(prose('theorem t (x : ℝ) : (↑(f x) : ℂ) = 0'), 'Let $x \\in \\mathbb{R}$. Let $\\iota$ be the canonical map into $\\mathbb{C}$. Then');
  const bare = toLatex('theorem t : (↑(1 : ℕ) : ℝ) = 1', 't', '');
  assert.equal(bare.thesis, '\\iota\\left(1 : \\mathbb{N}\\right) = 1');
  assert.equal(bare.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''), 'Let $\\iota$ be the canonical map into $\\mathbb{R}$. Then');
});

test('coercions: several maps in one statement are told apart by where they land', () => {
  const r = toLatex('theorem t (n : ℕ) : (↑(↑n : ℝ) : ℂ) = (↑n : ℂ)', 't', '');
  assert.equal(r.thesis, '\\iota_{\\mathbb{C}}\\left(\\iota_{\\mathbb{R}}\\left(n\\right)\\right) = \\iota_{\\mathbb{C}}\\left(n\\right)');
  assert.equal(r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''),
    'Let $n \\in \\mathbb{N}$. Let $\\iota_{\\mathbb{R}}$, $\\iota_{\\mathbb{C}}$ be the canonical maps into $\\mathbb{R}$, $\\mathbb{C}$. Then');
});

test('coercions: source text without Lean gives no target, and the map is still named', () => {
  const r = toLatex('theorem cast_succ (n : ℕ) : ↑(n + 1) = ↑n + 1', 'Nat.cast_succ', '');
  assert.equal(r.thesis, '\\iota\\left(n + 1\\right) = \\iota\\left(n\\right) + 1');
  assert.equal(r.parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join(''),
    'Let $n \\in \\mathbb{N}$. Let $\\iota$ be the canonical map from $\\mathbb{N}$. Then');
  assert.equal(expr('↑(r / s) = ↑r / ↑s'), '\\iota\\left(\\frac{r}{s}\\right) = \\frac{\\iota\\left(r\\right)}{\\iota\\left(s\\right)}');
  assert.equal(expr('(↑(Real.cos x) : ℂ) = Complex.cos (↑x : ℂ)'), '\\iota_{\\mathbb{C}}\\left(\\cos\\,x\\right) = \\cos\\,\\iota_{\\mathbb{C}}\\left(x\\right)');
  assert.equal(expr('((↑) : ℚ → ℝ)'), '\\left(\\left(\\uparrow\\right) : \\mathbb{Q} \\to \\mathbb{R}\\right)'); // the map itself, unapplied
});

test('a statement without coercions is untouched', () => {
  assert.equal(prose('theorem t (x : ℝ) (h : 0 < x) : 0 ≤ x'), 'Let $x \\in \\mathbb{R}$. Assume $0 < x$. Then');
});

test('the non-negative rationals ℚ≥0 are one symbol, like ℝ≥0', () => {
  assert.equal(expr('(q : ℚ≥0) ≤ 1'), '\\left(q : \\mathbb{Q}_{\\ge 0}\\right) \\le 1');
  assert.equal(prose('theorem t (q : ℚ≥0) : 0 ≤ q'), 'Let $q \\in \\mathbb{Q}_{\\ge 0}$. Then');
});

test('standard spaces are written with their usual symbol, not their Lean name', () => {
  assert.equal(expr('θ ∈ Real.Angle'), '\\theta \\in \\mathbb{R}/2\\pi\\mathbb{Z}');
  assert.equal(expr('x ∈ UnitAddCircle'), 'x \\in \\mathbb{R}/\\mathbb{Z}');
  assert.equal(expr('z ∈ Circle'), 'z \\in \\mathbb{S}^{1}');
  assert.equal(expr('f : NNReal → ENNReal'), 'f : \\mathbb{R}_{\\ge 0} \\to [0, \\infty]');
  assert.equal(expr('x : EReal'), 'x : [-\\infty, +\\infty]');
  assert.equal(expr('f : Nat → Int → Rat → Real → Complex'), 'f : \\mathbb{N} \\to \\mathbb{Z} \\to \\mathbb{Q} \\to \\mathbb{R} \\to \\mathbb{C}');
  assert.equal(expr('a : ZMod n'), 'a : \\mathbb{Z}/n\\mathbb{Z}');
  assert.equal(expr('a : ZMod (p ^ k)'), 'a : \\mathbb{Z}/p^{k}\\mathbb{Z}');
  assert.equal(expr('x : AddCircle T'), 'x : \\mathbb{R}/T\\mathbb{Z}');
  assert.equal(expr('x : ℚ_[p]'), 'x : \\mathbb{Q}_{p}');
  assert.equal(expr('x : ℤ_[p]'), 'x : \\mathbb{Z}_{p}');
  assert.equal(expr('σ : Equiv.Perm α'), '\\sigma : \\operatorname{Sym}\\left(\\alpha\\right)');
  assert.equal(expr('A : Matrix m n R'), 'A : \\mathrm{M}_{m \\times n}\\left(R\\right)');
  assert.equal(expr('u : Rˣ'), 'u : R^{\\times}');
});

test('standard spaces: a variable of such a type is "in" it, and a cast into it names it', () => {
  assert.equal(prose('theorem t (θ : Real.Angle) : θ = θ'), 'Let $\\theta \\in \\mathbb{R}/2\\pi\\mathbb{Z}$. Then');
  assert.equal(prose('theorem tan_coe (x : ℝ) : Real.Angle.tan (↑x : Real.Angle) = Real.tan x', '', 'Real.Angle.tan_coe'),
    'Let $x \\in \\mathbb{R}$. Let $\\iota : \\mathbb{R} \\to \\mathbb{R}/2\\pi\\mathbb{Z}$ be the canonical map. Then');
  // inside the Real namespace the source writes a bare `Angle`
  assert.equal(prose('theorem t (θ : Angle) : θ = θ', '', 'Real.Angle.t'), 'Let $\\theta \\in \\mathbb{R}/2\\pi\\mathbb{Z}$. Then');
  assert.equal(prose('theorem t (θ : Angle) : θ = θ', '', 'Foo.t'), 'Let $\\theta \\in \\mathrm{Angle}$. Then');
});

test('standard spaces: only when used as such', () => {
  assert.equal(expr('ZMod'), '\\mathrm{ZMod}'); // not applied
  assert.equal(expr('Foo.Angle'), '\\mathrm{Foo.Angle}');
  assert.equal(expr('Matrix m n'), '\\mathrm{Matrix}\\,m\\,n'); // an argument is missing
});

test('a function written after its argument with a dot: (x).tan is tan(x)', () => {
  assert.equal(toLatex('theorem tan_coe (x : ℝ) : (↑x : Real.Angle).tan = Real.tan x', 'Real.Angle.tan_coe', '').thesis, '\\tan\\left(\\iota\\left(x\\right)\\right) = \\tan\\,x');
  assert.equal(prose('theorem tan_coe (x : ℝ) : (↑x : Real.Angle).tan = Real.tan x', '', 'Real.Angle.tan_coe'),
    'Let $x \\in \\mathbb{R}$. Let $\\iota : \\mathbb{R} \\to \\mathbb{R}/2\\pi\\mathbb{Z}$ be the canonical map. Then');
  assert.equal(expr('(a + b).exp'), '\\exp\\left(a + b\\right)');
  assert.equal(expr('(a + b).foo'), '\\left(a + b\\right).\\mathrm{foo}');
});

test('castRule: a statement that says the same thing on both sides once the casts are erased', () => {
  const { castRule } = require('../public/lean-latex.js');
  assert.equal(castRule('theorem ofReal_div (r s : ℝ) : (↑(r / s) : ℂ) = (↑r : ℂ) / (↑s : ℂ)', 'Complex.ofReal_div', ''), true);
  assert.equal(castRule('theorem cast_add (m n : ℕ) : (↑(m + n) : R) = (↑m : R) + (↑n : R)', 'Nat.cast_add', ''), true);
  assert.equal(castRule('theorem tan_coe (x : ℝ) : (↑x : Real.Angle).tan = Real.tan x', 'Real.Angle.tan_coe', ''), true); // tan on angles, tan on reals
  assert.equal(castRule('theorem cast_le {m n : ℕ} : (↑m : ℝ) ≤ (↑n : ℝ) ↔ m ≤ n', 'Nat.cast_le', ''), true);
  assert.equal(castRule('theorem cast_inj {m n : ℕ} : (↑m : ℝ) = (↑n : ℝ) ↔ m = n', 'Nat.cast_inj', ''), true);
  assert.equal(castRule('theorem cast_succ (n : ℕ) : ↑(n + 1) = ↑n + 1', 'Nat.cast_succ', ''), true); // source text, no types
});

test('castRule: a statement with content is not one, cast or no cast', () => {
  const { castRule } = require('../public/lean-latex.js');
  assert.equal(castRule('theorem coe_two_pi : (↑(2 * π) : Real.Angle) = 0', 'Real.Angle.coe_two_pi', ''), false); // 2π is the zero angle: a fact
  assert.equal(castRule('theorem natCast_self (n : ℕ) : (↑n : ZMod n) = 0', 'ZMod.natCast_self', ''), false);
  assert.equal(castRule('theorem t (x : ℝ) : x = x', 't', ''), false); // no cast at all
  assert.equal(castRule('theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x', 'Real.sqrt_nonneg', ''), false);
  assert.equal(castRule('theorem t (n : ℕ) : (↑n : ℝ) < (↑n : ℝ) + 1', 't', ''), false);
  assert.equal(castRule('def f (n : ℕ) : ℝ', 'f', ''), false);
  assert.equal(castRule('structure S where', 'S', ''), false);
});

test('structured maps: a decorated arrow says what kind of map', () => {
  assert.equal(expr('f : M →ₗ[R] N'), 'f : M \\xrightarrow{R\\text{-linear}} N');
  assert.equal(expr('e : M ≃ₗ[R] N'), 'e : M \\xrightarrow[R\\text{-linear}]{\\sim} N');
  assert.equal(expr('f : R →+* S'), 'f : R \\xrightarrow{\\text{ring}} S');
  assert.equal(expr('f : G →* H'), 'f : G \\xrightarrow{\\text{group}} H');
  assert.equal(expr('f : A →+ B'), 'f : A \\xrightarrow{\\text{additive}} B');
  assert.equal(expr('f : E →L[𝕜] F'), 'f : E \\xrightarrow{\\Bbbk\\text{-linear, continuous}} F');
  assert.equal(expr('f : A →ₐ[R] B'), 'f : A \\xrightarrow{R\\text{-algebra}} B');
  assert.equal(expr('e : R ≃+* S'), 'e : R \\xrightarrow[\\text{ring}]{\\sim} S');
  assert.equal(expr('f : α →o β'), 'f : \\alpha \\xrightarrow{\\text{monotone}} \\beta');
  assert.equal(expr('f : α ↪ β'), 'f : \\alpha \\hookrightarrow \\beta');
  assert.equal(expr('e : α ≃ β'), 'e : \\alpha \\simeq \\beta');
  assert.equal(expr('F : C ⥤ D'), 'F : C \\xrightarrow{\\text{functor}} D');
  assert.equal(expr('f : α →₀ M'), 'f : \\alpha \\xrightarrow{\\text{finite support}} M');
});

test('structured maps: a variable of such a type is a map, written with a colon', () => {
  assert.equal(prose('theorem t (f : M →ₗ[R] N) (e : R ≃+* S) (x : M) : f x = f x'),
    'Let $f : M \\xrightarrow{R\\text{-linear}} N$, $e : R \\xrightarrow[\\text{ring}]{\\sim} S$, $x \\in M$. Then');
  assert.equal(expr('a → b'), 'a \\to b'); // the plain arrow is untouched
  assert.equal(expr('a →+ b + c'), 'a \\xrightarrow{\\text{additive}} b + c');
});

test('more spaces: power set, finite subsets, polynomials, power series', () => {
  assert.equal(expr('S : Set (Set α)'), 'S : \\mathcal{P}\\left(\\mathcal{P}\\left(\\alpha\\right)\\right)');
  assert.equal(expr('s : Finset ℕ'), 's : \\mathcal{P}_{\\mathrm{fin}}\\left(\\mathbb{N}\\right)');
  assert.equal(expr('p : R[X]'), 'p : R[X]');
  assert.equal(expr('p : Polynomial R'), 'p : R[X]');
  assert.equal(expr('p : (ZMod n)[X]'), 'p : \\left(\\mathbb{Z}/n\\mathbb{Z}\\right)[X]');
  assert.equal(expr('f : R⟦X⟧'), 'f : R [\\![ X ]\\!]');
  assert.equal(expr('l[i]'), 'l\\,\\left[i\\right]'); // indexing is not a polynomial ring
  // as a binder, a set is still "a subset of"
  assert.equal(prose('theorem t (s : Set α) (t : Finset α) : s = s'), 'Let $s \\subseteq \\alpha$, $t \\in \\mathcal{P}_{\\mathrm{fin}}\\left(\\alpha\\right)$. Then');
});

test('sides: the two sides of a rule that is an equation or an equivalence, and nothing else', () => {
  const { sides } = require('../public/lean-latex.js');
  assert.deepEqual(sides('a - b = 0 \\iff a = b'), ['a - b = 0', 'a = b']);
  assert.deepEqual(sides('\\cos x - \\cos y = -2 \\cdot \\sin \\left(\\frac{x + y}{2}\\right)'), ['\\cos x - \\cos y', '-2 \\cdot \\sin \\left(\\frac{x + y}{2}\\right)']);
  assert.deepEqual(sides('p = \\mathrm{False}'), ['p', '\\mathrm{False}']);
  assert.deepEqual(sides('\\left(a = b\\right) = \\left(b = a\\right)'), ['\\left(a = b\\right)', '\\left(b = a\\right)']);
  // not of that shape: an implication, a statement about all x, an "or" of equations, an inequality
  assert.equal(sides('p \\to a = b'), null);
  assert.equal(sides('\\forall x,\\; a = x'), null);
  assert.equal(sides('\\forall x,\\; a x \\iff b x'), null);
  assert.equal(sides('a = 0 \\lor b = 0'), null);
  assert.equal(sides('x = y \\lor z'), null);
  assert.equal(sides('2 \\ne 0'), null);
});

test('bound variables that Lean prints with their type: "there is n in ℤ", without brackets', () => {
  assert.equal(expr('∃ (n : ℤ), n = x'), expr('∃ n : ℤ, n = x'));
  assert.equal(expr('∃ (n : ℤ), n = x'), '\\exists n \\in \\mathbb{Z},\\; n = x');
  assert.equal(expr('∀ (x : ℝ), ∃ (n : ℕ), x < n'), expr('∀ x : ℝ, ∃ n : ℕ, x < n'));
  // several groups: one quantifier each, which says the same
  assert.equal(expr('∃ (a : ℕ) (b : ℤ), a = b'), expr('∃ a : ℕ, ∃ b : ℤ, a = b'));
  assert.equal(expr('∃ (a b : ℕ), a = b'), expr('∃ a b : ℕ, a = b'));
  assert.equal(expr('∃! (x : ℝ), f x = 0'), expr('∃! x : ℝ, f x = 0'));
  // a type with brackets of its own
  assert.equal(expr('∃ (p : ℕ × (ℤ × ℤ)), q p'), expr('∃ p : ℕ × (ℤ × ℤ), q p'));
});

test('typed variables of a function, a union, an integral: shown as before, the type left out', () => {
  assert.equal(expr('fun (x : ℝ) ↦ x + 1'), expr('fun x ↦ x + 1'));
  assert.equal(expr('fun (x : ℝ) (i j : ι) => f x i j'), expr('fun x i j => f x i j'));
  assert.equal(expr('⋃ (i : ι), s i'), expr('⋃ i, s i'));
  assert.equal(expr('∫ (x : E × ℝ), f x ∂μ'), expr('∫ x, f x ∂μ'));
  assert.equal(expr('∀ᶠ (n : ι) in l, p n'), expr('∀ᶠ n in l, p n'));
  assert.equal(expr("∑' (n : ι), f n"), expr("∑' n, f n"));
  // brackets that are not a typed variable are left alone
  assert.equal(expr('∀ (x) (y), x = y'), '\\forall \\left(x\\right)\\,\\left(y\\right),\\; x = y');
  assert.equal(expr('f (x : ℝ)'), 'f\\,\\left(x : \\mathbb{R}\\right)');
});

test('a canonical map applied to a bound variable: its source is that variable\'s type', () => {
  const tex = toLatex('theorem sin_eq_zero_iff {x : ℝ} : Real.sin x = 0 ↔ ∃ (n : ℤ), (↑n : ℝ) * π = x', 'Real.sin_eq_zero_iff', '');
  assert.ok(tex.parts.some((p) => p.math === '\\iota : \\mathbb{Z} \\to \\mathbb{R}'), JSON.stringify(tex.parts));
  // the same name bound twice with different types: no source is claimed
  const two = toLatex('theorem t : (∃ (n : ℤ), (↑n : ℝ) = 0) ∧ ∃ (n : ℕ), (↑n : ℝ) = 1', 't', '');
  assert.ok(!two.parts.some((p) => p.math && p.math.startsWith('\\iota :')), JSON.stringify(two.parts));
});

test('the conclusion on its own, away from the sentence that introduces the map: the map carries its target', () => {
  const tex = toLatex('theorem sin_eq_zero_iff {x : ℝ} : Real.sin x = 0 ↔ ∃ (n : ℤ), (↑n : ℝ) * π = x', 'Real.sin_eq_zero_iff', '');
  assert.equal(tex.thesis, '\\sin\\,x = 0 \\iff \\exists n \\in \\mathbb{Z},\\; \\iota\\left(n\\right) \\cdot \\pi = x');
  assert.equal(tex.thesisAlone, '\\sin\\,x = 0 \\iff \\exists n \\in \\mathbb{Z},\\; \\iota_{\\mathbb{R}}\\left(n\\right) \\cdot \\pi = x');
  const plain = toLatex('theorem mul_comm (a b : ℝ) : a * b = b * a', 'mul_comm', '');
  assert.equal(plain.thesisAlone, plain.thesis);
});
