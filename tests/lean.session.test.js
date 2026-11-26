const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { LeanStatements, statementFrom } = require('../lib/lean');

const fake = path.join(__dirname, 'fixtures', 'fake-lean.js');
const fakeSteps = path.join(__dirname, 'fixtures', 'fake-steps.js');
const tmp = () => path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'mathical-lean-')), 'cache.db');
const start = (mode = 'ok', cachePath = tmp()) =>
  new LeanStatements({ cachePath, command: process.execPath, args: [fake, mode] });

test('statementFrom turns what Lean prints into a statement with its keyword and short name', () => {
  assert.equal(statementFrom('Real.continuousOn_cos', 'theorem', 'Real.continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s'),
    'theorem continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s');
  assert.equal(statementFrom('Real.sqrt', 'definition', 'Real.sqrt (x : ℝ) : ℝ'), 'def sqrt (x : ℝ) : ℝ');
  assert.equal(statementFrom('Module.End', 'abbrev', 'Module.End (R : Type u) (M : Type v) : Type v'), 'abbrev End (R : Type u) (M : Type v) : Type v');
  assert.equal(statementFrom('Foo', 'inductive', 'Foo : Type'), null); // not a kind the converter renders
  assert.equal(statementFrom('Thm', 'theorem', 'Something.else : True'), null); // not the declaration asked for
  assert.equal(statementFrom('Thm', 'theorem', 'Thm :\n  1 =\n    1'), 'theorem Thm : 1 = 1'); // line breaks are Lean's layout, not content
});

test('asks Lean for statements, and remembers the answers', async () => {
  const cachePath = tmp();
  const lean = start('ok', cachePath);
  assert.deepEqual(lean.cached(['Thm']), {}); // nothing yet
  const got = await lean.statements([{ name: 'Thm', kind: 'theorem' }, { name: 'Hub', kind: 'definition' }, { name: 'Nope', kind: 'theorem' }]);
  assert.deepEqual(got, {
    Thm: 'theorem Thm {α : Type u_1} [Field α] (x : α) (h : x ≠ 0) : x / x = 1',
    Hub: 'def Hub {α : Type u_1} [Field α] (x : α) : α',
  });
  assert.equal(lean.state, 'ready');
  assert.deepEqual(lean.cached(['Thm', 'Nope', 'Other']), { Thm: got.Thm });
  await lean.close();

  // a new session on the same cache answers without Lean
  const offline = new LeanStatements({ cachePath, command: process.execPath, args: [fake, 'dies'] });
  assert.deepEqual(await offline.statements([{ name: 'Thm', kind: 'theorem' }, { name: 'Nope', kind: 'theorem' }]), { Thm: got.Thm });
  await offline.close();
});

test('when Lean cannot start, it answers from the cache only and says so', async () => {
  const lean = start('dies');
  assert.deepEqual(await lean.statements([{ name: 'Thm', kind: 'theorem' }]), {});
  assert.equal(lean.state, 'off');
  await lean.close();
});

test('without a command there is no Lean at all', async () => {
  const lean = new LeanStatements({ cachePath: tmp() });
  assert.equal(lean.state, 'off');
  assert.deepEqual(await lean.statements([{ name: 'Thm', kind: 'theorem' }]), {});
  await lean.close();
});

test('if Lean dies mid-way, pending questions are answered empty and later ones restart it', async () => {
  const lean = start('ok');
  await lean.statements([{ name: 'Thm', kind: 'theorem' }]);
  assert.deepEqual(await lean.statements([{ name: 'CRASH', kind: 'theorem' }, { name: 'Hub', kind: 'definition' }]), {});
  const again = await lean.statements([{ name: 'Hub', kind: 'definition' }]);
  assert.equal(again.Hub, 'def Hub {α : Type u_1} [Field α] (x : α) : α');
  await lean.close();
});

test('many questions at once all get their own answer', async () => {
  const lean = start('ok');
  const asks = Array.from({ length: 30 }, (_, i) => lean.statements([{ name: i % 2 ? 'Thm' : 'Real.continuousOn_cos', kind: 'theorem' }, { name: `Missing${i}`, kind: 'theorem' }]));
  const all = await Promise.all(asks);
  all.forEach((got, i) => assert.deepEqual(Object.keys(got), [i % 2 ? 'Thm' : 'Real.continuousOn_cos']));
  await lean.close();
});

test('what a declaration uses, in its statement and in its proof, is asked once and remembered', async () => {
  const cachePath = tmp();
  const lean = start('ok', cachePath);
  assert.deepEqual(await lean.uses(['Thm', 'Nope']), { Thm: { statement: ['Hub'], proof: ['A', 'Hub', 'B'] } });
  await lean.close();
  const offline = new LeanStatements({ cachePath, command: process.execPath, args: [fake, 'dies'] });
  assert.deepEqual(await offline.uses(['Thm', 'Nope', 'L1']), { Thm: { statement: ['Hub'], proof: ['A', 'Hub', 'B'] } });
  await offline.close();
});

test('whether a theorem is proved by reflexivity is asked once and remembered', async () => {
  const cachePath = tmp();
  const lean = start('ok', cachePath);
  assert.deepEqual(await lean.roles(['Thm', 'A', 'Nope']), { Thm: { rfl: false }, A: { rfl: true } });
  await lean.close();
  const offline = new LeanStatements({ cachePath, command: process.execPath, args: [fake, 'dies'] });
  assert.deepEqual(await offline.roles(['A', 'Nope', 'B']), { A: { rfl: true } });
  await offline.close();
});

test('the steps of a proof: a separate run of Lean on the source file, remembered afterwards', async () => {
  const cachePath = tmp();
  const lean = new LeanStatements({ cachePath, command: process.execPath, args: [fake], stepsArgs: [fakeSteps, 'ok'] });
  const steps = await lean.steps('Thm', 'Mathlib/Sample.lean');
  assert.equal(steps.length, 5);
  assert.equal(steps[1].text, 'add_zero');
  assert.equal(await lean.steps('Nope', 'Mathlib/Sample.lean'), null); // Lean ran and found nothing
  assert.equal(lean.state, 'idle'); // the session that answers statements was not needed
  await lean.close();
  // remembered: no Lean needed the second time, and "nothing" is remembered too
  const later = new LeanStatements({ cachePath });
  assert.equal((await later.steps('Thm', 'Mathlib/Sample.lean')).length, 5);
  assert.equal(await later.steps('Nope', 'Mathlib/Sample.lean'), null);
  assert.equal(await later.steps('Other', 'Mathlib/Sample.lean'), undefined); // not known, and no Lean to ask
  await later.close();
});

test('the steps of a proof: a run that fails is not remembered', async () => {
  const cachePath = tmp();
  const broken = new LeanStatements({ cachePath, command: process.execPath, args: [fake], stepsArgs: [fakeSteps, 'dies'] });
  assert.equal(await broken.steps('Thm', 'Mathlib/Sample.lean'), undefined);
  await broken.close();
  const fixed = new LeanStatements({ cachePath, command: process.execPath, args: [fake], stepsArgs: [fakeSteps, 'ok'] });
  assert.equal((await fixed.steps('Thm', 'Mathlib/Sample.lean')).length, 5);
  await fixed.close();
});
