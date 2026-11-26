// Stands in for `lake env lean --run lean/Steps.lean <file> <name>` in the tests.
const [mode, file, name] = process.argv.slice(2);
const goal = (id, target) => ({ id, case: '', target, hyps: [{ name: 'n', type: 'ℕ', prop: false, inst: false }] });
if (mode === 'dies') process.exit(3);
console.log('Lean chatter that is not ours');
if (name === 'Thm') {
  const g0 = goal('g0', 'n + 0 = n'), g1 = goal('g1', 'n = n');
  console.log(JSON.stringify({ name, file, steps: [
    { start: 4, stop: 12, kind: '@const', text: '', name: 'Core', before: [], after: [] }, // what the name refers to
    { start: 4, stop: 12, kind: 'null', text: 'add_zero', before: [g0], after: [g1] },
    { start: 12, stop: 13, kind: '«]»', text: ']', before: [g1], after: [] },
    { start: 0, stop: 13, kind: 'Lean.Parser.Tactic.rwSeq', text: 'rw [add_zero]', before: [g0], after: [] },
    { start: 0, stop: 13, kind: 'Lean.Parser.Term.byTactic', text: 'rw [add_zero]', before: [g0], after: [] },
  ] }));
} else console.log(JSON.stringify({ name, error: 'not declared in this file' }));
