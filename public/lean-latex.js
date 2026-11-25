// Rule-based Lean 4 statement -> LaTeX. It follows Lean's wording closely: binders become
// "Let … Assume …", the conclusion is typeset, and function application stays juxtaposition.
// A heuristic, not an elaborator: it knows notation, not meaning.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./lean-phrases.js'));
  else root.LeanLatex = factory(root.LeanPhrases);
})(this, function (Phrases) {
  'use strict';

  const PART = "[\\p{L}_][\\p{L}\\p{Nd}_'!?\\u2080-\\u209C\\u1D62-\\u1D6A]*";
  const IDENT = new RegExp(`${PART}(?:\\.${PART})*`, 'uy');
  const NUMBER = /\d+(?:\.\d+)?/y;
  const CLOSER = { '(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄' };
  const CLOSERS = new Set(Object.values(CLOSER));
  // Longest first: tokens that must not be split.
  const MULTI = ['ℝ≥0∞', 'ℝ≥0', 'Type*', 'Sort*', "⁻¹'", '⁻¹', '<->', ':=', '=>', '->', '<=', '>=', '..'];
  const SUPER = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9', 'ⁿ': 'n', '⁺': '+', '⁻': '-' };
  const BIGOPS = { '∑': '\\sum', '∏': '\\prod', '⋃': '\\bigcup', '⋂': '\\bigcap', '⨆': '\\bigsqcup', '⨅': '\\bigsqcap' };
  // Symbols that stand for a value (an operand)…
  const ATOMS = {
    'ℕ': '\\mathbb{N}', 'ℤ': '\\mathbb{Z}', 'ℚ': '\\mathbb{Q}', 'ℝ': '\\mathbb{R}', 'ℂ': '\\mathbb{C}',
    'ℝ≥0∞': '\\overline{\\mathbb{R}}_{\\ge 0}', 'ℝ≥0': '\\mathbb{R}_{\\ge 0}', 'Type*': '\\mathrm{Type}', 'Sort*': '\\mathrm{Sort}',
    '⊤': '\\top', '⊥': '\\bot', '∅': '\\emptyset', '∞': '\\infty', '_': '\\_', '·': '\\cdot', 'π': '\\pi', 'ℵ': '\\aleph',
  };
  // …and symbols that sit between or before operands.
  const OPS = {
    '→': '\\to', '->': '\\to', '↔': '\\iff', '<->': '\\iff', '↦': '\\mapsto', '=>': '\\mapsto',
    '∀': '\\forall', '∃': '\\exists', '¬': '\\neg', '∧': '\\land', '∨': '\\lor',
    '≤': '\\le', '<=': '\\le', '≥': '\\ge', '>=': '\\ge', '≠': '\\ne', '≡': '\\equiv', '≈': '\\approx', '≃': '\\simeq', '≅': '\\cong', '∼': '\\sim',
    '∈': '\\in', '∉': '\\notin', '⊆': '\\subseteq', '⊂': '\\subset', '⊇': '\\supseteq', '⊃': '\\supset',
    '∪': '\\cup', '∩': '\\cap', '⊔': '\\sqcup', '⊓': '\\sqcap', '∖': '\\setminus', '\\': '\\setminus',
    '×': '\\times', '*': '\\cdot', '•': '\\bullet', '∘': '\\circ', '∣': '\\mid', '⊗': '\\otimes', '⊕': '\\oplus', '⋆': '\\star',
    '∠': '\\angle', '∡': '\\measuredangle', '∫': '\\int', '∂': '\\partial', '∇': '\\nabla', '‖': '\\|', '⌊': '\\lfloor', '⌋': '\\rfloor', '⌈': '\\lceil', '⌉': '\\rceil',
    ',': ',\\;', '%': '\\%', '#': '\\#', '&': '\\&', '$': '\\$', '~': '\\sim', '..': '\\ldots', '≪': '\\ll', '≫': '\\gg', '⁅': '[', '⁆': ']',
    '⟶': '\\longrightarrow', '⟹': '\\Longrightarrow', '≫=': '\\gg', '⊢': '\\vdash', '∑': '\\sum', '∏': '\\prod',
  };
  const GREEK = {
    'α': 'alpha', 'β': 'beta', 'γ': 'gamma', 'δ': 'delta', 'ε': 'varepsilon', 'ζ': 'zeta', 'η': 'eta', 'θ': 'theta', 'ι': 'iota',
    'κ': 'kappa', 'μ': 'mu', 'ν': 'nu', 'ξ': 'xi', 'ρ': 'rho', 'σ': 'sigma', 'τ': 'tau', 'υ': 'upsilon', 'φ': 'varphi', 'χ': 'chi',
    'ψ': 'psi', 'ω': 'omega', 'Γ': 'Gamma', 'Δ': 'Delta', 'Θ': 'Theta', 'Λ': 'Lambda', 'Ξ': 'Xi', 'Σ': 'Sigma', 'Φ': 'Phi', 'Ψ': 'Psi', 'Ω': 'Omega',
  };
  const WORDS = { if: '\\text{if }', then: '\\text{ then }', else: '\\text{ else }', in: '\\text{ in }', at: '\\text{ at }', with: '\\text{ with }' };

  const unsub = (s) => s.replace(/[\u2080-\u2089]/g, (c) => String(c.charCodeAt(0) - 0x2080));

  function ident(name) {
    if (name === '𝕜') return '\\Bbbk';
    let m = /^([A-Za-z])(\d*)([\u2080-\u2089]*)('*)$/.exec(name);
    if (m) return m[1] + (m[2] || m[3] ? `_{${m[2]}${unsub(m[3])}}` : '') + m[4];
    m = /^(\p{Script=Greek})([\u2080-\u2089]*)('*)$/u.exec(name);
    if (m && GREEK[m[1]]) return `\\${GREEK[m[1]]}` + (m[2] ? `_{${unsub(m[2])}}` : '') + m[3];
    m = /^(.*?)([\u2080-\u2089]*)$/.exec(name);
    const body = unsub(m[1]).replace(/[_#%&${}]/g, (c) => '\\' + c).replace(/\^/g, '\\hat{}').replace(/~/g, '\\sim ');
    return `\\mathrm{${body}}` + (m[2] ? `_{${unsub(m[2])}}` : '');
  }

  function lex(src) {
    const out = [];
    let i = 0;
    scan: while (i < src.length) {
      const c = src[i];
      if (/\s/.test(c)) { i++; continue; }
      for (const m of MULTI) {
        if (src.startsWith(m, i)) { out.push({ t: 'sym', v: m }); i += m.length; continue scan; }
      }
      NUMBER.lastIndex = i;
      let m = NUMBER.exec(src);
      if (m) { out.push({ t: 'num', v: m[0] }); i += m[0].length; continue; }
      if (c in ATOMS || c in OPS || c in BIGOPS) { out.push({ t: 'sym', v: c }); i++; continue; }
      if (c in SUPER) {
        let v = '';
        while (src[i] in SUPER) v += SUPER[src[i++]];
        out.push({ t: 'sup', v });
        continue;
      }
      IDENT.lastIndex = i;
      m = IDENT.exec(src);
      if (m) { out.push({ t: 'id', v: m[0] }); i += m[0].length; continue; }
      if (c in CLOSER) out.push({ t: 'open', v: c });
      else if (CLOSERS.has(c)) out.push({ t: 'close', v: c });
      else out.push({ t: 'sym', v: c });
      i++;
    }
    return out;
  }

  // Nests bracketed runs: returns a list of tokens and { t: 'group', open, items }.
  function nest(tokens) {
    let i = 0;
    const seq = (closer) => {
      const items = [];
      while (i < tokens.length) {
        const tok = tokens[i++];
        if (tok.t === 'close') {
          if (tok.v !== closer) throw new Error('unbalanced brackets');
          return items;
        }
        if (tok.t === 'open') items.push({ t: 'group', open: tok.v, items: seq(CLOSER[tok.v]) });
        else items.push(tok);
      }
      if (closer) throw new Error('unbalanced brackets');
      return items;
    };
    return seq(null);
  }

  // `x : T` reads "x in T" when T is a collection of values: not a function type, not a universe.
  const isUniverse = (n) => n && ((n.t === 'id' && /^(Type|Sort|Prop)$/.test(n.v)) || n.v === 'Type*' || n.v === 'Sort*');
  const isArrow = (n) => n.t === 'sym' && (n.v === '→' || n.v === '->');
  const isComma = (n) => n.t === 'sym' && n.v === ',';
  const memberOf = (typeItems) => typeItems.length > 0 && !typeItems.some(isArrow) && !isUniverse(typeItems[0]);

  // `a < b ∧ b < c` is conventionally written `a < b < c`. Merges conjunctions whose parts are
  // order relations pointing the same way and whose shared middle term is written identically.
  const UP = new Set(['<', '≤', '<=', '=']), DOWN = new Set(['>', '≥', '>=', '=']);
  const OTHER_RELATIONS = new Set(['≠', '∈', '∉', '⊆', '⊂', '⊇', '⊃', '∣', '≡', '≈', '≃', '≅', '∼', '|']);
  const BOUNDARIES = new Set(['∧', '∨', '→', '->', '↔', '<->', ',', ':', ':=', '∀', '∃', '¬', '↦', '=>']);
  const sym = (n, set) => n.t === 'sym' && set.has(n.v);
  const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
  function mergeChains(items) {
    // Cut into segments at the boundary symbols, remembering each boundary.
    const segs = [[]], seps = [];
    for (const n of items) {
      if (sym(n, BOUNDARIES) || (n.t === 'id' && (n.v in WORDS || n.v === 'fun'))) { seps.push(n); segs.push([]); }
      else segs[segs.length - 1].push(n);
    }
    // A segment that is one chain of order relations: its relation positions and direction.
    const chain = (seg) => {
      if (seg.some((n) => sym(n, OTHER_RELATIONS))) return null;
      const at = seg.map((n, k) => (n.t === 'sym' && (UP.has(n.v) || DOWN.has(n.v)) ? k : -1)).filter((k) => k >= 0);
      if (!at.length || at[0] === 0 || at[at.length - 1] === seg.length - 1) return null;
      const rels = at.map((k) => seg[k].v);
      return { at, up: rels.every((r) => UP.has(r)), down: rels.every((r) => DOWN.has(r)) };
    };
    for (let k = 0; k + 1 < segs.length; ) {
      const and = seps[k].t === 'sym' && seps[k].v === '∧';
      const negated = k > 0 && seps[k - 1].t === 'sym' && seps[k - 1].v === '¬';
      const left = and && !negated ? chain(segs[k]) : null, right = left ? chain(segs[k + 1]) : null;
      const sameWay = left && right && ((left.up && right.up) || (left.down && right.down));
      if (sameWay && same(segs[k].slice(left.at[left.at.length - 1] + 1), segs[k + 1].slice(0, right.at[0]))) {
        segs[k] = [...segs[k], ...segs[k + 1].slice(right.at[0])];
        segs.splice(k + 1, 1);
        seps.splice(k, 1);
      } else k++;
    }
    return segs.flatMap((seg, k) => (k < seps.length ? [...seg, seps[k]] : seg));
  }

  // `x * x` is written x². A factor is a run of plain terms (names, numbers, bracketed groups);
  // identical factors joined by `*` collapse into a power, unless a neighbouring operator
  // that binds tighter (`/`, `^`, a superscript) would make that a different expression.
  const isTerm = (n) => n && (n.t === 'id' || n.t === 'num' || n.t === 'group') && !(n.t === 'id' && (n.v in WORDS || n.v === 'fun'));
  const isTimes = (n) => n && n.t === 'sym' && n.v === '*';
  const TIGHTER_BEFORE = new Set(['/', '^', '%', '•', '∘', '⁻¹', "⁻¹'", '√']);
  function mergePowers(items) {
    const out = [];
    let i = 0;
    while (i < items.length) {
      if (!isTerm(items[i])) { out.push(items[i++]); continue; }
      let end = i;
      while (isTerm(items[end])) end++;
      const factor = items.slice(i, end);
      let count = 1, next = end;
      while (isTimes(items[next]) && same(items.slice(next + 1, next + 1 + factor.length), factor) && !isTerm(items[next + 1 + factor.length])) {
        count++;
        next += 1 + factor.length;
      }
      const before = items[i - 1], after = items[next];
      const blocked = (before && (before.t === 'sup' || (before.t === 'sym' && TIGHTER_BEFORE.has(before.v)))) ||
        (after && (after.t === 'sup' || (after.t === 'sym' && (after.v === '^' || after.v === '⁻¹' || after.v === "⁻¹'"))));
      if (count > 1 && !blocked) {
        out.push(...factor, { t: 'sym', v: '^' }, { t: 'num', v: String(count) });
        i = next;
      } else {
        out.push(...factor);
        i = end;
      }
    }
    return out;
  }

  // `s : Set α` reads "s is a subset of α": true when the type is `Set` applied to one term.
  const isSetOf = (typeItems) => typeItems.length === 2 && typeItems[0].t === 'id' && typeItems[0].v === 'Set';

  // Set while converting a statement from Euclidean geometry, where |AB| is the usual
  // way to write the distance between two named points.
  let geometry = false;
  const isName = (n) => n && n.t === 'id' && !n.v.includes('.');

  // `binder` is true while rendering the inside of a quantifier's "(x : T)".
  function render(items, inSet, binder) {
    items = mergeChains(mergePowers(items));
    let quantified = false; // between a quantifier and its comma
    const out = []; // { s, atom }
    const atom = (s) => out.push({ s, atom: true });
    const op = (s) => out.push({ s, atom: false });
    const join = (list) => list.map((e, k) => (k ? (list[k - 1].atom && e.atom ? '\\,' : ' ') : '') + e.s).join('').replace(/ ,\\;/g, ',\\;');
    // The operand of a prefix or postfix operator, without its own parentheses.
    const inner = (node) => (!node ? '{}' : node.t === 'group' && node.open === '(' ? render(node.items) : render([node]));
    // In Lean `f x ^ 2` is `(f x) ^ 2`: a postfix applies to the whole application before it.
    const postfix = (s) => {
      let start = out.length;
      while (start > 0 && out[start - 1].atom) start--;
      const run = out.splice(start);
      if (!run.length) return atom('{}' + s);
      atom((run.length > 1 ? `\\left(${join(run)}\\right)` : run[0].s) + s);
    };
    for (let i = 0; i < items.length; i++) {
      const node = items[i];
      if (node.t === 'group') {
        const body = render(node.items, node.open === '{', quantified && node.open !== '⟨');
        if (node.open === '(') atom(`\\left(${body}\\right)`);
        else if (node.open === '[') atom(`\\left[${body}\\right]`);
        else if (node.open === '⟨') atom(`\\langle ${body} \\rangle`);
        else atom(`\\{ ${body} \\}`);
      } else if (node.t === 'num') atom(node.v);
      else if (node.t === 'sup') postfix(`^{${node.v}}`);
      else if (node.t === 'id') {
        if (node.v === 'fun' || node.v === 'λ') continue;
        if (node.v in WORDS) op(WORDS[node.v]);
        else if (node.v === 'dist' && isTerm(items[i + 1]) && isTerm(items[i + 2]) && !isTerm(items[i + 3])) {
          const a = items[i + 1], b = items[i + 2];
          if (geometry && isName(a) && isName(b)) atom(`\\lvert ${inner(a)} ${inner(b)} \\rvert`);
          else atom(`d\\left(${inner(a)}, ${inner(b)}\\right)`);
          i += 2;
        } else atom(ident(node.v));
      } else {
        const v = node.v;
        if (v === '√') atom(`\\sqrt{${inner(items[++i])}}`);
        else if (v === '^') postfix(`^{${inner(items[++i])}}`);
        else if (v === '⁻¹' || v === "⁻¹'") postfix('^{-1}'); // inverse, and preimage `f ⁻¹' s`
        else if (v === 'ᶜ') postfix('^{c}');
        else if (v in BIGOPS && items.slice(i + 1).some((n) => n.t === 'sym' && n.v === ',')) {
          const end = items.findIndex((n, k) => k > i && n.t === 'sym' && n.v === ',');
          op(`${BIGOPS[v]}_{${render(items.slice(i + 1, end))}}`);
          i = end;
        } else if (v === '↑' || v === '⇑' || v === '↥') {
          if (i + 1 >= items.length) atom('\\uparrow'); // a bare coercion; otherwise it is left out
        } else if (v === '@') continue;
        else if (v === ':' && (quantified || binder)) {
          const end = items.findIndex((n, k) => k > i && isComma(n));
          const type = items.slice(i + 1, end < 0 ? undefined : end);
          if (isSetOf(type)) {
            op('\\subseteq');
            atom(inner(type[1]));
            i += 2;
          } else op(memberOf(type) ? '\\in' : ':');
        } else if (v === '∀' || v === '∃') { quantified = true; op(OPS[v]); }
        else if (v === ',') { quantified = false; op(OPS[v]); }
        else if (v === '|' && inSet) op('\\mid');
        else if (v in ATOMS) atom(ATOMS[v]);
        else if (v in BIGOPS) op(BIGOPS[v]);
        else if (v in OPS) op(OPS[v]);
        else if (v === '{' || v === '}') op('\\' + v);
        else op(v);
      }
    }
    return join(out);
  }

  // One Lean expression as LaTeX math. Throws on unbalanced brackets.
  function expr(src) {
    return render(nest(lex(String(src))));
  }

  const RELATION = /[=≠≤<≥>∈∉⊆⊂↔∣∀∃¬∧∨≡]/;
  const NUMBER_SET = /^[ℕℤℚℝℂ]$/;
  const KINDS = { theorem: 'Theorem', lemma: 'Theorem', axiom: 'Axiom', def: 'Definition', abbrev: 'Definition', opaque: 'Definition', instance: 'Instance' };
  const HEAD = /^(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public|scoped|local|meta)\s+)*(theorem|lemma|axiom|def|abbrev|opaque|instance)\b\s*(?:\(priority[^)]*\)\s*)?/;

  // Index of the first `ch` outside any brackets (and not part of `:=`), or -1.
  function topLevel(s, ch, from = 0) {
    let depth = 0;
    for (let i = from; i < s.length; i++) {
      const c = s[i];
      if (c in CLOSER) depth++;
      else if (CLOSERS.has(c)) depth--;
      else if (depth === 0 && s.startsWith(ch, i) && !(ch === ':' && s[i + 1] === '=')) return i;
    }
    return -1;
  }
  const hasTopLevel = (s, re) => {
    let depth = 0;
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (c in CLOSER) depth++;
      else if (CLOSERS.has(c)) depth--;
      else if (depth === 0 && re.test(c) && !(c === '=' && (s[i + 1] === '>' || s[i - 1] === ':'))) return true;
    }
    return false;
  };

  // "Module ℝ (E × F)" -> ["Module", "ℝ", "(E × F)"]: split at spaces outside brackets.
  function splitTop(s) {
    const out = [];
    let depth = 0, cur = '';
    for (const c of s) {
      if (c in CLOSER) depth++;
      else if (CLOSERS.has(c)) depth--;
      if (/\s/.test(c) && depth === 0) { if (cur) out.push(cur); cur = ''; } else cur += c;
    }
    if (cur) out.push(cur);
    return out;
  }

  // Splits "(a b : T) {c : U} [Inst] : conclusion" into binders and the conclusion.
  function signatureParts(s) {
    const binders = [];
    let i = 0;
    for (;;) {
      while (/\s/.test(s[i] || '')) i++;
      const open = s[i];
      if (!(open in CLOSER) || open === '⟨') break;
      let depth = 0, j = i;
      for (; j < s.length; j++) {
        if (s[j] in CLOSER) depth++;
        else if (CLOSERS.has(s[j]) && --depth === 0) break;
      }
      if (j >= s.length) throw new Error('unbalanced binder');
      binders.push({ open, body: s.slice(i + 1, j).trim() });
      i = j + 1;
    }
    const rest = s.slice(i);
    const colon = topLevel(rest, ':');
    if (colon < 0) return { binders, bare: rest.trim(), conclusion: null };
    return { binders, bare: rest.slice(0, colon).trim(), conclusion: rest.slice(colon + 1).trim() };
  }

  // The names a piece of Lean text mentions (for `a.b`, both `a.b` and `a`).
  const mentioned = (text) => lex(text).filter((t) => t.t === 'id').flatMap((t) => [t.v, t.v.split('.')[0]]);

  // The `variable` binders the statement depends on, as Lean would include them: a named
  // variable when something mentions its name, an instance when it is about such a variable.
  function inScope(context, statementText, ownBinders) {
    if (!context) return [];
    let all;
    try { all = signatureParts(context).binders; } catch { return []; }
    const namesOf = (b) => {
      const colon = topLevel(b.body, ':');
      return b.open === '[' ? [] : (colon < 0 ? b.body : b.body.slice(0, colon)).trim().split(/\s+/).filter(Boolean);
    };
    const own = new Set(ownBinders.flatMap(namesOf)); // redeclared by the statement itself
    const used = new Set(mentioned(statementText).filter((n) => !own.has(n)));
    const kept = new Map(); // binder -> the names of it that are used (all of an instance)
    for (let changed = true; changed; ) {
      changed = false;
      for (const b of all) {
        const colon = topLevel(b.body, ':');
        const type = colon < 0 ? (b.open === '[' ? b.body : '') : b.body.slice(colon + 1);
        const before = kept.get(b) ? kept.get(b).length : -1;
        let now;
        if (b.open === '[') now = mentioned(type).slice(2).some((n) => used.has(n)) ? [] : null; // skip the class itself
        else { now = namesOf(b).filter((n) => used.has(n) && !own.has(n)); if (!now.length) now = null; }
        if (!now || now.length === before) continue;
        kept.set(b, now);
        mentioned(type).forEach((n) => { if (!own.has(n)) used.add(n); });
        changed = true;
      }
    }
    return all.filter((b) => kept.has(b)).map((b) => {
      if (b.open === '[') return b;
      const colon = topLevel(b.body, ':');
      return { open: b.open, body: kept.get(b).join(' ') + (colon < 0 ? '' : ' ' + b.body.slice(colon)) };
    });
  }

  // Returns { kind, parts, source } or null when the statement is not one this can render.
  // `parts` alternate prose ({ text }) and formulas ({ math, display? }); `source` is LaTeX.
  // `context` is the binder text of the `variable` commands in scope, if known.
  function toLatex(statement, fullName, context) {
    geometry = /^EuclideanGeometry\./.test(String(fullName || ''));
    try {
      let s = String(statement || '').replace(/\/--[\s\S]*?-\//g, '').trim();
      while (s.startsWith('@[')) {
        const end = s.indexOf(']');
        if (end < 0) return null;
        s = s.slice(end + 1).trim();
      }
      const head = HEAD.exec(s);
      if (!head) return null;
      const kind = KINDS[head[1]];
      s = s.slice(head[0].length);
      const declared = /^[^\s:({\[⦃]+/.exec(s);
      if (declared) s = s.slice(declared[0].length);
      const name = fullName || (declared ? declared[0] : '');
      const { binders, bare, conclusion } = signatureParts(s);
      if (!conclusion) return null;

      const vars = [], insts = [], hyps = [];
      const subjects = [], about = new Map(), typeVars = new Set(); // what the typeclasses talk about
      const subject = (name) => { if (!about.has(name)) { about.set(name, []); subjects.push(name); } return about.get(name); };
      if (bare) vars.push(bare.split(/\s+/).map(ident).join(', '));
      for (const b of [...inScope(context, s, binders), ...binders]) {
        const colon = topLevel(b.body, ':');
        if (b.open === '[') {
          const type = (colon < 0 ? b.body : b.body.slice(colon + 1)).trim();
          const [head, ...args] = splitTop(type);
          const cls = (head || '').replace(/\.\{[^}]*\}$/, ''); // `Category.{v} C`: drop the universe annotation
          const what = Phrases.classify(cls, args);
          if (what.kind === 'hyp') hyps.push(expr(what.lean));
          else if (what.kind === 'about') subject(what.subject).push({ cls, args });
          else if (what.kind === 'unknown') insts.push(expr(type));
          continue;
        }
        const names = (colon < 0 ? b.body : b.body.slice(0, colon)).trim().split(/\s+/).filter(Boolean);
        let type = colon < 0 ? '' : b.body.slice(colon + 1);
        const dflt = topLevel(type, ':=');
        if (dflt >= 0) type = type.slice(0, dflt); // drop a default value
        type = type.trim();
        if (!type) { vars.push(names.map(ident).join(', ')); continue; }
        if (/^(Type|Sort)\b/.test(type)) { names.forEach((n) => { typeVars.add(n); subject(n); }); continue; }
        // Hypotheses are usually called h, hx, h₁ … or given a descriptive name such as f_mble.
        const named = names.every((n) => /^h[\p{L}\p{N}_'₀-₉]*$/u.test(n) || n.includes('_')) && !NUMBER_SET.test(type) && !/^Prop\b/.test(type);
        if (hasTopLevel(type, RELATION) || named) hyps.push(expr(type));
        else {
          const typeItems = nest(lex(type));
          const shown = names.map(ident).join(', ');
          if (isSetOf(typeItems)) vars.push(`${shown} \\subseteq ${render(typeItems[1].t === 'group' && typeItems[1].open === '(' ? typeItems[1].items : [typeItems[1]])}`);
          else vars.push(`${shown} ${memberOf(typeItems) ? '\\in' : ':'} ${expr(type)}`);
        }
      }

      // "Let V be a real inner product space, and let P be …": one clause per subject.
      const classesOf = (name) => new Set((about.get(name) || []).map((i) => i.cls));
      const clauses = [];
      for (const name of subjects) {
        const instances = about.get(name);
        const said = instances.length ? Phrases.describe(instances, { isType: typeVars.has(name), classesOf }) : null;
        if (said) { clauses.push({ names: [name], said }); continue; }
        instances.forEach((i) => insts.push(expr([i.cls, ...i.args].join(' ')))); // nothing to say: keep Lean's wording
        if (!typeVars.has(name)) continue;
        const last = clauses[clauses.length - 1];
        if (last && !last.said) last.names.push(name);
        else clauses.push({ names: [name] });
      }

      const parts = [];
      const text = (t) => {
        const last = parts[parts.length - 1];
        if (last && 'text' in last) last.text += t;
        else parts.push({ text: t });
      };
      const sentence = (opening) => text((parts.length ? '. ' : '') + opening);
      const series = (items, each) => items.forEach((item, k) => {
        if (k) text(k === items.length - 1 ? ' and ' : ', ');
        each(item);
      });
      const list = (items, each) => items.forEach((item, k) => { if (k) text(', '); each(item); });
      clauses.forEach((clause, k) => {
        if (k === 0) sentence('Let ');
        else text(k === clauses.length - 1 ? ', and let ' : ', let ');
        series(clause.names, (name) => parts.push({ math: ident(name) }));
        if (!clause.said) { text(clause.names.length > 1 ? ' be types' : ' be a type'); return; }
        text(' be ');
        clause.said.forEach((piece) => (typeof piece === 'string' ? text(piece) : parts.push({ math: expr(piece.lean) })));
      });
      if (vars.length) { sentence('Let '); list(vars, (v) => parts.push({ math: v })); }
      if (insts.length) {
        if (vars.length) text(', with ');
        else sentence('Given ');
        list(insts, (v) => parts.push({ math: v }));
      }
      if (hyps.length) {
        sentence('Assume ');
        // Lean's names for the hypotheses (h, hx, …) are left out: prose does not label them.
        series(hyps, (h) => parts.push({ math: h }));
      }
      if (parts.length) text('. Then');
      const shown = kind === 'Theorem' || kind === 'Axiom' ? expr(conclusion) : `${ident(name)} : ${expr(conclusion)}`;
      parts.push({ math: shown, display: true });

      const env = kind === 'Theorem' || kind === 'Axiom' ? 'theorem' : 'definition';
      const prose = parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join('');
      const source = [
        `\\begin{${env}}[\\texttt{${name.replace(/[_#%&${}]/g, (c) => '\\' + c)}}]`,
        ...(prose ? [prose] : []),
        `\\[ ${shown} \\]`,
        `\\end{${env}}`,
      ].join('\n');
      return { kind, parts, source };
    } catch {
      return null;
    } finally {
      geometry = false;
    }
  }

  return { expr, toLatex };
});
