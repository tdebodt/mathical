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
    target: g.target === worked.target ? null : g.target,
    learned: listed(g.hyps.filter((x) => !known.has(`${x.name}\n${x.type}`))),
  }));
  return { results, closes: !fresh.length && !step.after.some((g) => g.id === worked.id) };
}

// ---------- a step in plain words ----------
// A proof step is written as a command to Lean (`constructor`, `rcases h with ⟨n, hn⟩`).
// For the commands met most often, what the step does, in the words a written proof would
// use. Where the same command does different things (`constructor` on "A ⟺ B" and on
// "A and B"), the goals Lean recorded decide. Anything else is left as Lean wrote it.

// Steps that do their work inside: what they are for.
const AUTOMATIC = {
  simp: 'simplify', simp_all: 'simplify', simp_rw: 'simplify', dsimp: 'unfold definitions', simpa: 'simplify',
  norm_num: 'compute with the numerals', ring: 'an identity valid in every commutative ring', ring_nf: 'normalise as a polynomial expression',
  linarith: 'linear arithmetic from the hypotheses', nlinarith: 'arithmetic from the hypotheses and their products',
  positivity: 'positive because its parts are', omega: 'linear arithmetic over the integers', field_simp: 'clear the denominators',
  abel: 'an identity valid in every abelian group', group: 'an identity valid in every group',
  aesop: 'found by automatic search', grind: 'found by automatic search', tauto: 'follows by logic alone', decide: 'checked by direct computation',
  norm_cast: 'move the embeddings between number systems', push_cast: 'move the embeddings between number systems',
  exact_mod_cast: 'conclude, up to the embeddings between number systems',
  fun_prop: 'follows from how the function is built', continuity: 'follows from how the function is built',
  measurability: 'follows from how the function is built', infer_instance: 'a structure that is already known',
};
const PLAIN = {
  left: 'prove the left alternative', right: 'prove the right alternative',
  use: 'take as the witness', exists: 'take as the witness',
  by_cases: 'two cases: it holds, or it does not', contrapose: 'prove the contrapositive instead',
  exfalso: 'derive a contradiction instead', symm: 'swap the two sides',
  congr: 'reduce to the corresponding parts being equal', calc: 'a chain of steps',
  convert: 'this is the fact cited, up to the differences left to prove',
  specialize: 'apply the hypothesis to particular values', subst: 'substitute throughout',
  filter_upwards: 'it is enough to prove it where the facts listed hold, since they hold eventually',
  classical: 'allow deciding any statement (classical logic)',
  choose: 'choose a function that gives such a witness for each input',
  lift: 'regard it as an element of the smaller type', rwa: 'rewrite, then conclude with a hypothesis',
  nth_rw: 'rewrite one occurrence', nth_rewrite: 'rewrite one occurrence',
  trans: 'go through an intermediate term', transitivity: 'go through an intermediate term',
  replace: 'replace the hypothesis by a new version', apply_fun: 'apply a function to both sides',
  push_neg: 'push the negation inward', gcongr: 'compare the two sides part by part',
  assumption: 'this is one of the hypotheses', rfl: 'both sides are the same by definition',
  trivial: 'immediate', contradiction: 'the hypotheses contradict each other',
  suffices: 'it suffices to prove', nontriviality: 'set the trivial case aside',
  conv_lhs: 'work on the left-hand side only', conv_rhs: 'work on the right-hand side only',
};

function inWords(text, worked, results) {
  if (text.includes('<;>')) return null; // several commands in one
  const word = (/^[A-Za-z_][\w?']*/.exec(text) || [''])[0];
  const rest = text.slice(word.length).replace(/^!/, '').trim();
  const at = (/\bat\s+(.+)$/.exec(rest) || [])[1];
  const learned = results[0] ? results[0].learned : [];
  const objects = learned.filter((x) => !x.prop).map((x) => x.name).join(', ');
  const facts = learned.filter((x) => x.prop).map((x) => x.name).join(', ');
  const n = results.length;
  switch (word) {
    case 'constructor':
      if (n === 2 && worked && worked.target.includes(' ↔ ') && results.every((r) => r.target && r.target.includes(' → '))) return 'prove the two directions separately';
      return n > 1 ? `prove the ${n} parts separately` : 'build the statement from its parts';
    case 'intro': case 'intros': case 'rintro': {
      if (/[⟨|]/.test(rest)) { // a pattern: the assumption is taken apart as it comes in
        if (n > 1) return `assume the premise and split it into ${n} cases`;
        const names = [objects, facts].filter(Boolean).join(', ');
        return 'assume the premise' + (names ? `; from it, obtain ${names}` : ' and take it apart');
      }
      const parts = [objects && `take ${objects} arbitrary`, facts && `assume the premise, as ${facts}`].filter(Boolean);
      if (!parts.length) return 'introduce what the statement quantifies over';
      return parts.join('; ') + (n > 1 ? `, in ${n} cases` : '');
    }
    case 'rcases': case 'obtain': case 'cases': case "cases'": {
      const subject = word === 'obtain' ? '' : (/^(.+?)\s+with\b/.exec(rest) || [])[1] || '';
      if (n > 1) {
        // Why there are cases, when the hypothesis taken apart is an "or"; and what every
        // case provides, when they all provide the same names.
        const hyp = worked && worked.hyps.find((x) => x.name === subject);
        const head = hyp && hyp.type.includes(' ∨ ') ? `${subject} is an "or": ${n} cases` : `split ${subject || 'it'} into ${n} cases`;
        const given = results.map((r) => r.learned.map((x) => x.name).filter((name) => name !== subject).join(', '));
        return head + (given[0] && given.every((names) => names === given[0]) ? `; in each, it provides ${given[0]}` : '');
      }
      const names = [objects, facts].filter(Boolean).join(', ');
      if (!names) return subject ? `take ${subject} apart` : 'obtain';
      return subject ? `from ${subject}, obtain ${names}` : `obtain ${names}`;
    }
    case 'exact': return 'conclude with';
    case 'apply': return n ? 'it is enough to prove the premises of' : 'conclude by applying';
    case 'refine': case "refine'": return n ? 'reduce to the gaps (?_) left in' : 'conclude with';
    case 'have': case 'haveI': return facts ? `intermediate claim ${facts}` : 'intermediate claim';
    case 'let': case 'letI': case 'set': return objects ? `define ${objects}` : 'define';
    case 'show': case 'change': return `restate ${at || 'what is to prove'} (the same by definition)`;
    case 'by_contra': return 'by contradiction: assume the opposite' + (facts ? `, as ${facts}` : '');
    case 'induction': case "induction'": return rest ? `by induction on ${rest.split(/\s+/)[0]}` : 'by induction';
    case 'ext': case 'ext1': case 'funext': return 'prove the equality pointwise' + (objects ? `: take ${objects} arbitrary` : '');
    case 'unfold': case 'delta': return 'replace by its definition';
    default:
  }
  if (Object.hasOwn(AUTOMATIC, word)) {
    const does = AUTOMATIC[word];
    if (word === 'simpa' && /\busing\b/.test(rest)) return 'simplify, then conclude with the fact given (automatic)';
    if (!at) return `${does} (automatic)`;
    return (does === 'simplify' ? `simplify ${at}` : `${does}, in ${at}`) + ' (automatic)';
  }
  return Object.hasOwn(PLAIN, word) ? PLAIN[word] : null;
}

function arrange(recorded) {
  if (!recorded || !recorded.length) return null;
  // Besides the steps, Lean reports each name in the proof that it resolved to a declaration.
  const cited = recorded.filter((s) => s.kind === '@const');
  const raw = recorded.filter((s) => s.kind !== '@const');
  if (!raw.length) return null;
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
    if (!isRule(s) && !BULLET.test(s.kind) && !/[\p{L}\p{N}]/u.test(s.text)) continue; // `;` and the like
    if (kept.some((k) => sameRange(k, s))) continue;
    kept.push(s);
  }
  kept.sort((a, b) => a.start - b.start || b.stop - a.stop);
  const bullets = raw.filter((s) => BULLET_BLOCK.test(s.kind));
  // Bullets side by side are the cases of one split: each gets its number among them.
  const holderOf = (b) => {
    const around = raw.filter((s) => inside(b, s));
    const nearest = around.length ? around.reduce((x, y) => (y.stop - y.start < x.stop - x.start ? y : x)) : null;
    return nearest ? `${nearest.start}:${nearest.stop}` : '';
  };
  const numberOf = (b) => bullets.filter((o) => holderOf(o) === holderOf(b) && o.start <= b.start).length;
  // Which case a step is in, counting from the outermost: "1.2" is the second case inside the first.
  const pathOf = (s) => bullets.filter((b) => inside(s, b)).sort((x, y) => x.start - y.start).map(numberOf).join('.');
  const numbering = (tk) => {
    const own = bullets.find((b) => b.start === tk.start);
    if (!own) return {};
    const beside = bullets.filter((b) => holderOf(b) === holderOf(own)).sort((x, y) => x.start - y.start);
    return { number: beside.findIndex((b) => b.start === own.start) + 1, of: beside.length, label: pathOf(tk) };
  };

  // What is known in a goal beyond what the proof started with: a case opens with it.
  const atStart = new Set((first ? first.hyps : []).map((x) => `${x.name}\n${x.type}`));
  const beyondStart = (g) => listed(g.hyps.filter((x) => !atStart.has(`${x.name}\n${x.type}`)));

  const steps = kept.map((s) => {
    const isCase = BULLET.test(s.kind);
    const holders = kept.filter((k) => inside(s, k)).length + bullets.filter((b) => inside(s, b)).length;
    const child = kept.find((k) => inside(k, s));
    const own = child ? Buffer.from(s.text).subarray(0, child.start - s.start).toString() : s.text;
    const ownStop = child ? child.start : s.stop;
    const backwards = isRule(s) && /^\s*(←|<-)/.test(own); // `← rule`: used from right to left
    const out = {
      kind: isCase ? 'case' : 'step',
      within: pathOf(s),
      depth: Math.max(0, holders - (isCase ? 1 : 0)),
      text: oneLine(isRule(s) ? own.replace(/,\s*$/, '').replace(/^\s*(←|<-)/, '') : own),
      rewrite: isRule(s),
      backwards,
      cites: [...new Set(cited.filter((c) => s.start <= c.start && c.stop <= ownStop).map((c) => c.name))],
    };
    if (isCase) return { ...out, ...numbering(s), says: null, results: s.after[0] ? [{ target: s.after[0].target, learned: beyondStart(s.after[0]) }] : [], closes: false };
    Object.assign(out, resultsOf(s));
    out.says = out.rewrite ? null : inWords(out.text, s.before[0], out.results);
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
