// The steps of a proof, chosen from everything Lean recorded while checking it
// (lean/Steps.lean). Lean records a step for every piece of tactic syntax: each tactic, each
// rule inside `rw [a, b]`, but also every block that merely holds other steps, and some
// steps twice under two names. This picks the ones a reader follows, in the order of the
// text, and says for each what it left to prove and what it made known.

// Syntax that only groups other steps.
const BLOCK = /(^|\.)(tacticSeq|tacticSeq1Indented|tacticSeqBracketed|byTactic|paren)$|^by$/;
const BULLET_BLOCK = /(^|\.)cdot$/; // `· tactics`: one case
const BULLET = /(^|\.)cdotTk$/; // the `·` itself

const sameRange = (a, b) => a.start === b.start && a.stop === b.stop;
const inside = (a, b) => b.start <= a.start && a.stop <= b.stop && !sameRange(a, b);
const listed = (hyps) => hyps.filter((x) => !x.inst).map(({ name, type, prop }) => ({ name, type, prop }));
const oneLine = (text) => text.replace(/\s+/g, ' ').trim();

// What a step made of the goal it worked on: the goals that are new after it, each with its
// statement (null when that did not change) and the hypotheses that were not there before.
function resultsOf(step) {
  const worked = step.before[0];
  if (!worked) return { results: [], closes: false };
  const had = new Set(step.before.map((g) => g.id));
  const fresh = step.after.filter((g) => !had.has(g.id));
  const known = new Set(worked.hyps.map((x) => `${x.name}\n${x.type}`));
  const results = fresh.map((g) => ({
    target: fresh.length === 1 && g.target === worked.target ? null : g.target,
    learned: listed(g.hyps.filter((x) => !known.has(`${x.name}\n${x.type}`))),
  }));
  return { results, closes: !fresh.length && !step.after.some((g) => g.id === worked.id) };
}

function arrange(raw) {
  if (!raw || !raw.length) return null;
  const whole = raw.reduce((widest, s) => (s.stop - s.start > widest.stop - widest.start ? s : widest));
  const first = whole.before[0];
  // A rule of a rewrite is recorded without a name of its own, once; anything else recorded
  // without a name is a second record of a named step.
  const isRule = (s) => s.kind === 'null' && !raw.some((o) => o !== s && o.kind !== 'null' && sameRange(o, s));
  const rules = raw.filter(isRule);
  // The rewrite a rule belongs to: the smallest step around it. Its rules stand for it.
  const rewrites = [];
  for (const rule of rules) {
    const around = raw.filter((s) => !isRule(s) && inside(rule, s));
    if (!around.length) continue;
    const nearest = around.reduce((a, b) => (b.stop - b.start < a.stop - a.start ? b : a));
    rule.of = nearest;
    if (!rewrites.includes(nearest)) rewrites.push(nearest);
  }
  const replaced = (s) => rewrites.some((r) => sameRange(r, s));
  const closing = (s) => s.text === ']' && rewrites.some((r) => inside(s, r));

  const kept = [];
  for (const s of raw) {
    if (BLOCK.test(s.kind) || BULLET_BLOCK.test(s.kind) || replaced(s) || closing(s)) continue;
    if (s.kind === 'null' && !isRule(s)) continue;
    if (kept.some((k) => sameRange(k, s))) continue;
    kept.push(s);
  }
  kept.sort((a, b) => a.start - b.start || b.stop - a.stop);
  const bullets = raw.filter((s) => BULLET_BLOCK.test(s.kind));

  const steps = kept.map((s) => {
    const isCase = BULLET.test(s.kind);
    const holders = kept.filter((k) => inside(s, k)).length + bullets.filter((b) => inside(s, b)).length;
    const child = kept.find((k) => inside(k, s));
    const own = child ? Buffer.from(s.text).subarray(0, child.start - s.start).toString() : s.text;
    const out = {
      kind: isCase ? 'case' : 'step',
      depth: Math.max(0, holders - (isCase ? 1 : 0)),
      text: oneLine(isRule(s) ? own.replace(/,\s*$/, '') : own),
      rewrite: isRule(s),
    };
    if (isCase) return { ...out, results: s.after[0] ? [{ target: s.after[0].target, learned: [] }] : [], closes: false };
    Object.assign(out, resultsOf(s));
    if (s.of) {
      const at = /\]\s*at\s+(.+)$/s.exec(s.of.text);
      if (at) out.at = oneLine(at[1]);
      // After its last rule a rewrite checks whether both sides are now the same.
      const bracket = raw.find((o) => o.text === ']' && inside(o, s.of));
      const last = !rules.some((r) => r.of === s.of && r.start > s.start);
      if (last && bracket && resultsOf(bracket).closes) out.closes = true;
    }
    return out;
  });
  return { goal: first ? first.target : null, given: first ? listed(first.hyps) : [], steps };
}

module.exports = { arrange };
