// The outline of a Lean tactic proof: its intermediate claims, case splits and local
// definitions, in order, with the author's comments, and a count of the tactic lines in
// between. It reads the proof's text line by line; it does not run Lean, so it shows what
// the author wrote down, not the goals Lean had at each step.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.LeanOutline = factory();
})(this, function () {
  'use strict';

  const OPEN = '([{⟨⦃', CLOSE = ')]}⟩⦄';

  // Index of the first place, outside brackets, where `test(text, i)` holds; or -1.
  function topLevel(text, test, from = 0) {
    let depth = 0;
    for (let i = from; i < text.length; i++) {
      const c = text[i];
      if (OPEN.includes(c)) depth++;
      else if (CLOSE.includes(c)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && test(text, i)) return i;
    }
    return -1;
  }
  const isAssign = (t, i) => t[i] === ':' && t[i + 1] === '=';
  const isColon = (t, i) => t[i] === ':' && t[i + 1] !== '=';
  // Where the statement of a step ends and its justification begins: `:=`, ` by`, ` from`.
  const isEnd = (t, i) => isAssign(t, i) || (/\s/.test(t[i]) && /^\s+(by|from)(\s|$)/.test(t.slice(i, i + 7)));

  const indentOf = (line) => line.length - line.trimStart().length;
  const tidy = (s) => s.replace(/\s+/g, ' ').trim();

  // Returns the steps of the proof `body` (the source text from ":=" on): a list of
  //   { kind: 'note',     depth, text }               a comment by the author
  //   { kind: 'claim',    depth, label, binders, lean } `have label binders : lean`
  //   { kind: 'obtain',   depth, label, lean }          `obtain ⟨label⟩ : lean`
  //   { kind: 'suffices', depth, label, lean }          it suffices to show `lean`
  //   { kind: 'show',     depth, lean }                 the goal restated
  //   { kind: 'cases',    depth, label, lean }          split on whether `lean` holds
  //   { kind: 'let',      depth, lean }                 a local definition, "x := e"
  //   { kind: 'calc',     depth, lean }                 a chain "a = b ≤ c"
  //   { kind: 'intro',    depth, text }                 names introduced
  //   { kind: 'induction', depth, text }                the variable of an induction
  //   { kind: 'tactics',  depth, count }                that many other proof lines
  // `depth` is the nesting level. A proof that is a term, not tactics, gives [].
  function outline(body) {
    const text = String(body || '');
    const first = /^\s*:=\s*by\b(.*)$/.exec(text.split('\n')[0] || '');
    if (!first) return [];
    const rest = text.split('\n').slice(1);
    const base = Math.min(...rest.filter((l) => l.trim()).map(indentOf), Infinity);
    const lines = [...(first[1].trim() ? [' '.repeat(Number.isFinite(base) ? base : 2) + first[1].trim()] : []), ...rest];
    const unit = Number.isFinite(base) ? base : 2;

    const steps = [];
    const push = (step) => steps.push(step);
    const tactic = (depth) => {
      const last = steps[steps.length - 1];
      if (last && last.kind === 'tactics' && last.depth === depth) last.count++;
      else push({ kind: 'tactics', depth, count: 1 });
    };

    for (let i = 0; i < lines.length; i++) {
      let line = lines[i];
      if (!line.trim()) continue;
      let indent = indentOf(line), content = line.trim();
      // A focusing dot opens a sub-proof: what follows it sits one level in.
      while (/^[·.]\s/.test(content)) { content = content.slice(1).trimStart(); indent += 2; }
      const depth = Math.max(0, Math.round((indent - unit) / 2));

      if (content.startsWith('--')) {
        const note = content.replace(/^--+\s?/, '').trim();
        const last = steps[steps.length - 1];
        if (!note) continue;
        if (last && last.kind === 'note' && last.depth === depth) last.text += ' ' + note;
        else push({ kind: 'note', depth, text: note });
        continue;
      }

      const word = /^([A-Za-z_']+)/.exec(content);
      const keyword = word ? word[1] : '';

      // The statement of this step, joined over its continuation lines, up to its justification.
      const statement = (needsEnd) => {
        let whole = content, end = topLevel(whole, isEnd);
        while (needsEnd && end < 0 && i + 1 < lines.length && lines[i + 1].trim() && indentOf(lines[i + 1]) > indentOf(line)) {
          whole += ' ' + lines[++i].trim();
          end = topLevel(whole, isEnd);
        }
        return tidy(end < 0 ? whole : whole.slice(0, end)).slice(keyword.length).trim();
      };

      if (keyword === 'have' || keyword === 'haveI' || keyword === 'replace') {
        const head = statement(true);
        const colon = topLevel(head, isColon);
        if (colon < 0) { tactic(depth); continue; } // `have := foo`: nothing is stated
        const before = head.slice(0, colon).trim();
        const named = /^[^\s({\[⟨⦃]+/.exec(before);
        push({ kind: 'claim', depth, label: named ? named[0] : 'this', binders: tidy(named ? before.slice(named[0].length) : before), lean: tidy(head.slice(colon + 1)) });
      } else if (keyword === 'obtain' || keyword === 'rcases') {
        const head = statement(true);
        const colon = topLevel(head, isColon);
        if (keyword === 'rcases' || colon < 0) { tactic(depth); continue; }
        push({ kind: 'obtain', depth, label: tidy(head.slice(0, colon)).replace(/^⟨|⟩$/g, ''), lean: tidy(head.slice(colon + 1)) });
      } else if (keyword === 'suffices') {
        const head = statement(true);
        const colon = topLevel(head, isColon);
        const before = colon < 0 ? '' : head.slice(0, colon).trim();
        const labelled = colon >= 0 && /^[^\s({\[⟨⦃∀∃]+$/.test(before); // `suffices h : p`, not `suffices ∀ x : α, p`
        push({ kind: 'suffices', depth, label: labelled ? before : '', lean: tidy(labelled ? head.slice(colon + 1) : head) });
      } else if (keyword === 'show') {
        push({ kind: 'show', depth, lean: statement(false) });
      } else if (keyword === 'by_cases') {
        const head = statement(false);
        const colon = topLevel(head, isColon);
        const labelled = colon >= 0 && /^\S+$/.test(head.slice(0, colon).trim());
        push({ kind: 'cases', depth, label: labelled ? head.slice(0, colon).trim() : '', lean: tidy(labelled ? head.slice(colon + 1) : head) });
      } else if (keyword === 'set' || keyword === 'let') {
        const whole = tidy(content.slice(keyword.length));
        const assign = topLevel(whole, isAssign);
        if (assign < 0) { tactic(depth); continue; }
        const colon = topLevel(whole.slice(0, assign), isColon);
        const name = tidy(colon < 0 ? whole.slice(0, assign) : whole.slice(0, colon));
        let value = whole.slice(assign + 2);
        const withAt = topLevel(value, (t, k) => /^\s+with\s/.test(t.slice(k, k + 6)));
        if (withAt >= 0) value = value.slice(0, withAt);
        // A value that starts on the next line (a structure being built) is not shown: say what is being named.
        if (!tidy(value)) push({ kind: 'let', depth, lean: colon < 0 ? name : `${name} : ${tidy(whole.slice(colon + 1, assign))}` });
        else push({ kind: 'let', depth, lean: `${name} := ${tidy(value)}` });
      } else if (keyword === 'calc') {
        // The steps are the first relation and every line starting with `_`; the lines in
        // between are their proofs.
        const calcIndent = indentOf(line);
        const links = [];
        const add = (stepText) => {
          const end = topLevel(stepText, isAssign);
          const link = tidy(end < 0 ? stepText : stepText.slice(0, end));
          if (link) links.push(links.length ? link.replace(/^_\s*/, '') : link);
        };
        if (content.slice(4).trim()) add(content.slice(4));
        while (i + 1 < lines.length && (!lines[i + 1].trim() || indentOf(lines[i + 1]) > calcIndent)) {
          const next = lines[++i].trim();
          if (next && (!links.length || next.startsWith('_'))) add(next);
        }
        if (links.length) push({ kind: 'calc', depth, lean: links.join(' ') });
        else tactic(depth);
      } else if (depth === 0 && (keyword === 'intro' || keyword === 'intros') && content.slice(keyword.length).trim()) {
        // Only at the top: inside a sub-proof an `intro` is a detail of that step.
        push({ kind: 'intro', depth, text: tidy(content.slice(keyword.length)) });
      } else if (/^induction'?$/.test(keyword) && /^induction'?\s+\S+/.test(content)) {
        push({ kind: 'induction', depth, text: /^induction'?\s+(\S+)/.exec(content)[1] });
      } else tactic(depth);
    }
    return steps;
  }

  return { outline };
});
