// Lean 4 colouring and dependency linking, shared by the page and the tests.
// A lexer by regular expressions, not a Lean parser.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.Lean = factory();
})(this, function () {
  'use strict';

  const words = (s) => new Set(s.trim().split(/\s+/));
  const KEYWORDS = words(`
    theorem lemma def abbrev instance structure class inductive opaque axiom example alias
    noncomputable private protected public scoped local unsafe partial nonrec mutual
    where by fun let have show from at with using match if then else do in open namespace
    section end variable universe deriving extends return for forall exists calc suffices
    termination_by decreasing_by set_option attribute import module notation infix infixl infixr
    macro syntax Type Prop Sort`);
  const TACTICS = words(`
    simp simpa simp_all simp_rw dsimp rw rwa rewrite erw nth_rw nth_rewrite exact exact_mod_cast
    apply refine refine' intro intros rintro rcases obtain cases cases' induction induction'
    constructor use ext funext congr gcongr norm_num norm_cast push_cast linarith nlinarith
    positivity omega ring ring_nf field_simp aesop tauto decide trivial rfl unfold change convert
    specialize by_contra by_contra! by_cases contrapose contrapose! push_neg left right exfalso
    assumption infer_instance fun_prop conv subst symm trans filter_upwards lift choose
    classical grind bound abel group nlinarith split split_ifs set replace generalize
    exists absurd contradiction calc_step case next all_goals any_goals first repeat try
    on_goal swap rotate_left exacts refine apply_fun congrm measurability continuity
    interval_cases fin_cases lia order mono peel wlog borelize delta injection native_decide
    simp? aesop? exact? apply? rw?`);

  const PART = "[\\p{L}_][\\p{L}\\p{N}_'!?\\u2080-\\u209C\\u1D62-\\u1D6A]*";
  const IDENT = new RegExp(`${PART}(?:\\.${PART})*`, 'uy');
  const NUMBER = /\d[\d_]*(?:\.\d+)?/y;

  // Splits Lean source into [{ type, text }]. Types: kw, tac, ident, comment, str, num,
  // attr, warn, text. Joining every `text` gives the input back.
  function tokenize(code) {
    const out = [];
    const push = (type, text) => {
      const last = out[out.length - 1];
      if (type === 'text' && last && last.type === 'text') last.text += text;
      else out.push({ type, text });
    };
    const until = (from, marker, type, start) => {
      const end = code.indexOf(marker, from);
      const stop = end < 0 ? code.length : end + marker.length;
      push(type, code.slice(start, stop));
      return stop;
    };
    let i = 0;
    while (i < code.length) {
      const c = code[i], d = code[i + 1];
      if (c === '/' && d === '-') { i = until(i + 2, '-/', 'comment', i); continue; }
      if (c === '-' && d === '-') {
        const end = code.indexOf('\n', i);
        const stop = end < 0 ? code.length : end;
        push('comment', code.slice(i, stop));
        i = stop;
        continue;
      }
      if (c === '"') {
        let j = i + 1;
        while (j < code.length && code[j] !== '"') j += code[j] === '\\' ? 2 : 1;
        j = Math.min(code.length, j + 1);
        push('str', code.slice(i, j));
        i = j;
        continue;
      }
      if (c === '@' && d === '[') { i = until(i + 2, ']', 'attr', i); continue; }
      NUMBER.lastIndex = i;
      let m = NUMBER.exec(code);
      if (m) { push('num', m[0]); i += m[0].length; continue; }
      IDENT.lastIndex = i;
      m = IDENT.exec(code);
      if (m) {
        const word = m[0];
        const type = word === 'sorry' ? 'warn' : KEYWORDS.has(word) ? 'kw' : TACTICS.has(word) ? 'tac' : 'ident';
        push(type, word);
        i += word.length;
        continue;
      }
      push('text', c);
      i++;
    }
    return out;
  }

  // Returns a function that splits one identifier, as written in a proof, into
  // [{ text, target? }], where `target` is the full name of the dependency that piece
  // refers to. Proofs use short names (`sqrt_nonneg` inside `namespace Real`) and dot
  // notation (`hp.not_isSquare` for `Nat.Prime.not_isSquare`), so a piece matches a
  // dependency when it equals its name or is a suffix of it on a dot boundary.
  function linker(deps, focusName) {
    const names = new Set(deps);
    const byLast = new Map();
    for (const name of names) {
      const last = name.slice(name.lastIndexOf('.') + 1);
      if (!byLast.has(last)) byLast.set(last, []);
      byLast.get(last).push(name);
    }
    const home = String(focusName || '').split('.').slice(0, -1);
    const closeness = (name) => {
      const parts = name.split('.');
      let n = 0;
      while (n < home.length && parts[n] === home[n]) n++;
      return n;
    };
    const resolve = (piece) => {
      if (names.has(piece)) return piece;
      if (piece.length === 1) return null; // a local variable, almost always
      const last = piece.slice(piece.lastIndexOf('.') + 1);
      const found = (byLast.get(last) || []).filter((name) => name.endsWith('.' + piece));
      if (!found.length) return null;
      return found.sort((a, b) => closeness(b) - closeness(a) || a.length - b.length || (a < b ? -1 : 1))[0];
    };
    return function link(ident) {
      const parts = ident.split('.');
      const out = [];
      const plain = (text) => {
        const last = out[out.length - 1];
        if (last && !last.target) last.text += text;
        else out.push({ text });
      };
      let i = 0;
      while (i < parts.length) {
        let matched = false;
        for (let j = parts.length - 1; j >= i; j--) {
          const piece = parts.slice(i, j + 1).join('.');
          const target = resolve(piece);
          if (target) {
            if (i > 0) plain('.');
            out.push({ text: piece, target });
            i = j + 1;
            matched = true;
            break;
          }
        }
        if (!matched) {
          plain((i > 0 ? '.' : '') + parts[i]);
          i++;
        }
      }
      return out;
    };
  }

  return { tokenize, linker };
});
