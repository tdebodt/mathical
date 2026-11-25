const { test } = require('node:test');
const assert = require('node:assert/strict');
const { tokenize, linker } = require('../public/lean.js');

const types = (code) => tokenize(code).filter((t) => t.type !== 'text').map((t) => [t.type, t.text]);

test('tokenize loses nothing', () => {
  const code = '@[simp]\ntheorem foo {p : ℕ} (h : 0 ≤ √x) : P := by\n  simp [bar, ← Nat.baz\'] -- note\n  /- block\n comment -/ exact "s\\"t" 42';
  assert.equal(tokenize(code).map((t) => t.text).join(''), code);
});

test('tokenize classifies keywords, tactics, identifiers, comments, strings, numbers, attributes', () => {
  assert.deepEqual(types('@[simp] theorem foo : P := by\n  simp [Nat.bar₁, h.1] -- note'), [
    ['attr', '@[simp]'], ['kw', 'theorem'], ['ident', 'foo'], ['ident', 'P'], ['kw', 'by'],
    ['tac', 'simp'], ['ident', 'Nat.bar₁'], ['ident', 'h'], ['num', '1'], ['comment', '-- note'],
  ]);
  assert.deepEqual(types('/- a\nb -/ exact "x -- y" 3.5 sorry'), [
    ['comment', '/- a\nb -/'], ['tac', 'exact'], ['str', '"x -- y"'], ['num', '3.5'], ['warn', 'sorry'],
  ]);
  assert.deepEqual(types("foo.mpr hp.not_isSquare simp_all x'"), [
    ['ident', 'foo.mpr'], ['ident', 'hp.not_isSquare'], ['tac', 'simp_all'], ['ident', "x'"],
  ]);
});

test('a keyword inside a dotted name is just part of the name', () => {
  assert.deepEqual(types('Nat.rec Function.end'), [['ident', 'Nat.rec'], ['ident', 'Function.end']]);
});

test('linker splits dot notation into the dependencies it names', () => {
  const link = linker(['Nat.prime_two', 'Nat.Prime.irrational_sqrt', 'Iff.mpr', 'Nat.Prime.not_isSquare'], 'irrational_sqrt_two');
  assert.deepEqual(link('Nat.prime_two.irrational_sqrt'), [
    { text: 'Nat.prime_two', target: 'Nat.prime_two' },
    { text: '.' },
    { text: 'irrational_sqrt', target: 'Nat.Prime.irrational_sqrt' },
  ]);
  assert.deepEqual(link('hp.not_isSquare'), [
    { text: 'hp.' }, { text: 'not_isSquare', target: 'Nat.Prime.not_isSquare' },
  ]);
  assert.deepEqual(link('foo.mpr'), [{ text: 'foo.' }, { text: 'mpr', target: 'Iff.mpr' }]);
  assert.deepEqual(link('unknown.thing'), [{ text: 'unknown.thing' }]);
});

test('linker resolves a short name to the dependency closest to the focus namespace', () => {
  const link = linker(['NNReal.sqrt_nonneg', 'Real.sqrt_nonneg', 'Foo.h', 'x'], 'Real.sqrt_le_sqrt');
  assert.deepEqual(link('sqrt_nonneg'), [{ text: 'sqrt_nonneg', target: 'Real.sqrt_nonneg' }]);
  assert.deepEqual(link('Real.sqrt_nonneg'), [{ text: 'Real.sqrt_nonneg', target: 'Real.sqrt_nonneg' }]);
  assert.deepEqual(link('h'), [{ text: 'h' }]); // a one-letter local name is never guessed
  assert.deepEqual(link('x'), [{ text: 'x', target: 'x' }]); // but an exact match is
  assert.deepEqual(link('qrt_nonneg'), [{ text: 'qrt_nonneg' }]); // suffixes match on dot boundaries only
});
