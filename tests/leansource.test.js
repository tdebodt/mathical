const { test } = require('node:test');
const assert = require('node:assert/strict');
const { findDeclaration, modulePath } = require('../lib/leansource');

const SRC = `module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open Rat Real

/-- A number is irrational if it is not rational. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_isSquare

/-- **Irrationality of the Square Root of 2** -/
theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt

namespace Irrational

variable {x : ℝ}

/--
If \`x\` is irrational,
so is \`x + q\`.
-/
@[simp]
protected theorem add_ratCast (h : Irrational x)
    (q : ℚ := 0) :
    Irrational (x + q) :=
  sorry

theorem _root_.foo_bar : True := trivial

section Inner
theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m := sorry
end Inner

def fib : ℕ → ℕ
  | 0 => 0
  | n + 1 => fib n

end Irrational

theorem ne_nat : False := sorry

@[simp] lemma one_line : 1 = 1 := rfl

instance (priority := 100) instFoo : Inhabited ℕ where
  default := 0

structure Point (α : Type) where
  x : α
  y : α
  deriving Repr

private theorem hidden_thing : True := trivial

theorem uses_it : irrational_sqrt_two = irrational_sqrt_two := rfl

end
`;

test('finds a top-level theorem with its docstring and line', () => {
  const r = findDeclaration(SRC, 'irrational_sqrt_two');
  assert.equal(r.statement, 'theorem irrational_sqrt_two : Irrational (√2)');
  assert.equal(r.doc, '**Irrationality of the Square Root of 2**');
  assert.equal(r.line, 17);
});

test('a dotted name declared outside a namespace', () => {
  assert.equal(
    findDeclaration(SRC, 'Nat.Prime.irrational_sqrt').statement,
    'theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p)'
  );
});

test('resolves names through namespaces, keeps attributes, ignores := inside binders', () => {
  const r = findDeclaration(SRC, 'Irrational.add_ratCast');
  assert.equal(
    r.statement,
    '@[simp]\nprotected theorem add_ratCast (h : Irrational x)\n    (q : ℚ := 0) :\n    Irrational (x + q)'
  );
  assert.equal(r.doc, 'If `x` is irrational,\nso is `x + q`.');
  assert.equal(r.line, 29);
});

test('the namespace decides between two declarations with the same short name', () => {
  assert.match(findDeclaration(SRC, 'Irrational.ne_nat').statement, /x ≠ m$/);
  assert.match(findDeclaration(SRC, 'ne_nat').statement, /False$/);
});

test('_root_ escapes the namespace', () => {
  assert.equal(findDeclaration(SRC, 'foo_bar').statement, 'theorem _root_.foo_bar : True');
  assert.equal(findDeclaration(SRC, 'Irrational.foo_bar'), null);
});

test('a definition stops at := and a pattern-matching one at the first case', () => {
  assert.equal(findDeclaration(SRC, 'Irrational').statement, 'def Irrational (x : ℝ)');
  assert.equal(findDeclaration(SRC, 'Irrational.fib').statement, 'def fib : ℕ → ℕ');
});

test('attribute on the same line, instances and structures', () => {
  assert.equal(findDeclaration(SRC, 'one_line').statement, '@[simp] lemma one_line : 1 = 1');
  assert.equal(findDeclaration(SRC, 'instFoo').statement, 'instance (priority := 100) instFoo : Inhabited ℕ');
  assert.equal(
    findDeclaration(SRC, 'Point').statement,
    'structure Point (α : Type) where\n  x : α\n  y : α\n  deriving Repr'
  );
});

test('private declarations are found under their mangled name', () => {
  const r = findDeclaration(SRC, '_private.Mathlib.NumberTheory.Real.Irrational.0.hidden_thing');
  assert.equal(r.statement, 'private theorem hidden_thing : True');
});

test('a mention inside a proof is not a declaration; unknown names give null', () => {
  assert.equal(findDeclaration(SRC, 'irrational_sqrt_two').line, 17);
  assert.equal(findDeclaration(SRC, 'Point.mk'), null);
  assert.equal(findDeclaration(SRC, 'nope'), null);
  assert.equal(findDeclaration('', 'nope'), null);
});

test('modulePath maps Mathlib modules only', () => {
  assert.equal(modulePath('Mathlib.Data.Real.Sqrt'), 'Mathlib/Data/Real/Sqrt.lean');
  assert.equal(modulePath('Init.Core'), null);
  assert.equal(modulePath(null), null);
  assert.equal(modulePath('Mathlib.../etc'), null);
});

test('redirects lists the imports of a deprecated shim file, and nothing for a normal file', () => {
  const { redirects } = require('../lib/leansource');
  const shim = 'module -- shake: keep-all\n\nimport Mathlib.Analysis.Real.Sqrt\npublic import Mathlib.Other.File\n\ndeprecated_module (since := "2026-05-28")\n';
  assert.deepEqual(redirects(shim), ['Mathlib/Analysis/Real/Sqrt.lean', 'Mathlib/Other/File.lean']);
  assert.deepEqual(redirects(SRC), []);
});

test('body is the proof or definition that follows the statement', () => {
  const body = (n) => findDeclaration(SRC, n).body;
  assert.equal(body('irrational_sqrt_two'), ':= by\n  simpa using Nat.prime_two.irrational_sqrt');
  assert.equal(body('Irrational'), ':=\n  x ∉ Set.range ((↑) : ℚ → ℝ)');
  assert.equal(body('Irrational.add_ratCast'), ':=\n  sorry');
  assert.equal(body('Irrational.fib'), '  | 0 => 0\n  | n + 1 => fib n');
  assert.equal(body('instFoo'), 'where\n  default := 0');
  assert.equal(body('one_line'), ':= rfl');
  assert.equal(body('uses_it'), ':= rfl'); // stops at the closing `end`
  assert.equal(body('Point'), null); // a structure's fields are already in the statement
});

test('body keeps blank lines inside a proof and stops at the next command', () => {
  const src = [
    'theorem t : P := by', '  have a := 1', '', '  exact a', '', '/-- next -/', 'theorem u : Q := sorry', '',
    'def f (n : ℕ) : ℕ :=', '  if n = 0 then 0 else f (n - 1)', 'termination_by n', 'decreasing_by omega', '',
    'open Foo in', 'theorem v : R := sorry',
  ].join('\n');
  assert.equal(findDeclaration(src, 't').body, ':= by\n  have a := 1\n\n  exact a');
  assert.equal(findDeclaration(src, 'u').body, ':= sorry');
  assert.equal(findDeclaration(src, 'f').body, ':=\n  if n = 0 then 0 else f (n - 1)\ntermination_by n\ndecreasing_by omega');
});

test('a very long body is returned whole', () => {
  const src = 'theorem big : P := by\n' + Array.from({ length: 900 }, (_, i) => `  step ${i}`).join('\n') + '\n';
  const r = findDeclaration(src, 'big');
  assert.equal(r.body.split('\n').length, 901);
  assert.match(r.body, /step 899$/);
  assert.equal('truncated' in r, false);
});

test('context: the `variable` declarations in scope at the declaration', () => {
  const src = [
    'variable {α : Type*}', '',
    'namespace Outer', '',
    'variable {V : Type*} {P : Type*} [NormedAddCommGroup V]', '  [NormedAddTorsor V P]', '',
    'section Inner', 'variable (x : α)', 'theorem a : x = x := rfl', 'end Inner', '',
    'theorem b (p : P) : p = p := rfl', '',
    'end Outer', '',
    'variable (n : ℕ) in', 'theorem c : True := trivial',
  ].join('\n');
  assert.equal(findDeclaration(src, 'Outer.a').context, '{α : Type*} {V : Type*} {P : Type*} [NormedAddCommGroup V] [NormedAddTorsor V P] (x : α)');
  assert.equal(findDeclaration(src, 'Outer.b').context, '{α : Type*} {V : Type*} {P : Type*} [NormedAddCommGroup V] [NormedAddTorsor V P]');
  assert.equal(findDeclaration(src, 'c').context, '{α : Type*}');
  assert.equal(findDeclaration(SRC, 'irrational_sqrt_two').context, '');
  assert.equal(findDeclaration(SRC, 'Irrational.add_ratCast').context, '{x : ℝ}');
});
