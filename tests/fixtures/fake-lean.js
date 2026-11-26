// Stands in for `lean --run lean/Signatures.lean` in tests: same protocol, canned answers.
const readline = require('node:readline');

const KNOWN = {
  Thm: 'Thm {α : Type u_1} [Field α] (x : α) (h : x ≠ 0) : x / x = 1',
  'Real.continuousOn_cos': 'Real.continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s',
  Hub: 'Hub {α : Type u_1} [Field α] (x : α) : α',
};

const mode = process.argv[2] || 'ok';
if (mode === 'dies') process.exit(3); // never becomes ready
const say = (o) => process.stdout.write(JSON.stringify(o) + '\n');

setTimeout(() => {
  say({ ready: true });
  readline.createInterface({ input: process.stdin }).on('line', (line) => {
    const name = line.trim();
    if (!name) return;
    if (name === 'CRASH') process.exit(1);
    if (Object.hasOwn(KNOWN, name)) say({ name, signature: KNOWN[name] });
    else say({ name, error: 'unknown declaration' });
  });
}, 30);
