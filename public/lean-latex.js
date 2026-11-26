// Rule-based Lean 4 statement -> LaTeX.
// It changes notation, never the statement: what Lean writes as an angle stays an angle, even
// where a textbook would say "orthogonal". An equivalent restatement is still a different claim. It follows Lean's wording closely: binders become
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
  const CLOSER = { '(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄', '⟪': '⟫' };
  const CLOSERS = new Set(Object.values(CLOSER));
  // Longest first: tokens that must not be split.
  const MULTI = ['ℝ≥0∞', 'ℝ≥0', 'ℚ≥0', 'Type*', 'Sort*', "⁻¹'", '⁻¹', "''", '-ᵥ', '+ᵥ', '<->', ':=', '=>', '->', '<=', '>=', '..'];
  // Mathlib's arrows for maps that respect a structure. Each is one sign; some take the
  // scalars in square brackets, `M →ₗ[R] N`. `iso` marks the two-way versions.
  const MAPS = {
    '→ₗᵢ': ['linear isometry', true], '≃ₗᵢ': ['linear isometry', true, true], '→ₛₗ': ['semilinear', true], '≃ₛₗ': ['semilinear', true, true],
    '→ₗ': ['linear', true], '≃ₗ': ['linear', true, true], '→ₐ': ['algebra', true], '≃ₐ': ['algebra', true, true],
    '→L': ['linear, continuous', true], '≃L': ['linear, continuous', true, true],
    '→+*': ['ring'], '≃+*': ['ring', false, true], '→+': ['additive'], '≃+': ['additive', false, true],
    '→*': ['group'], '≃*': ['group', false, true], '→o': ['monotone'], '≃o': ['order', false, true],
    '→ᵇ': ['bounded, continuous'], '→₀': ['finite support'], '≃ᵐ': ['measurable', false, true], '≃ₜ': ['homeomorphism', false, true],
    '≃ᵢ': ['isometry', false, true], '⥤': ['functor'],
  };
  const ARROW = new RegExp('^(?:' + Object.keys(MAPS).sort((a, b) => b.length - a.length).map((k) => k.replace(/[+*]/g, '\\$&')).join('|') + ')');
  const SUPER = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9', 'ⁿ': 'n', '⁺': '+', '⁻': '-' };
  const BIGOPS = { '∑': '\\sum', '∏': '\\prod', '⋃': '\\bigcup', '⋂': '\\bigcap', '⨆': '\\bigsqcup', '⨅': '\\mathop{\\sqcap}' };
  // Symbols that stand for a value (an operand)…
  const ATOMS = {
    'ℕ': '\\mathbb{N}', 'ℤ': '\\mathbb{Z}', 'ℚ': '\\mathbb{Q}', 'ℝ': '\\mathbb{R}', 'ℂ': '\\mathbb{C}',
    'ℝ≥0∞': '\\overline{\\mathbb{R}}_{\\ge 0}', 'ℝ≥0': '\\mathbb{R}_{\\ge 0}', 'ℚ≥0': '\\mathbb{Q}_{\\ge 0}', 'Type*': '\\mathrm{Type}', 'Sort*': '\\mathrm{Sort}',
    '⊤': '\\top', '⊥': '\\bot', '∅': '\\emptyset', '∞': '\\infty', '_': '\\_', '·': '\\cdot', 'π': '\\pi', 'ℵ': '\\aleph',
  };
  // …and symbols that sit between or before operands.
  const OPS = {
    '→': '\\to', '->': '\\to', '↪': '\\hookrightarrow', '≃': '\\simeq', '⟦': '[\\![', '⟧': ']\\!]', '↔': '\\iff', '<->': '\\iff', '↦': '\\mapsto', '=>': '\\mapsto',
    '∀': '\\forall', '∃': '\\exists', '¬': '\\neg', '∧': '\\land', '∨': '\\lor',
    '≤': '\\le', '<=': '\\le', '≥': '\\ge', '>=': '\\ge', '≠': '\\ne', '≡': '\\equiv', '≈': '\\approx', '≃': '\\simeq', '≅': '\\cong', '∼': '\\sim',
    '∈': '\\in', '∉': '\\notin', '⊆': '\\subseteq', '⊂': '\\subset', '⊇': '\\supseteq', '⊃': '\\supset',
    '∪': '\\cup', '∩': '\\cap', '⊔': '\\sqcup', '⊓': '\\sqcap', '∖': '\\setminus', '\\': '\\setminus',
    '-ᵥ': '-', '+ᵥ': '+', // difference of two points, and a vector added to a point
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

  // Names every mathematician writes with a standard sign. A name counts when it is bare or
  // sits in one of the namespaces where it has its usual meaning (Real.pi, Complex.exp, Nat.gcd);
  // `Finset.pi` or `Filter.exp` are other things and keep their Lean name.
  const STANDARD_NS = new Set(['', 'Real', 'Complex', 'NNReal', 'ENNReal', 'EReal', 'Nat', 'Int', 'Matrix']);
  const standard = (name) => {
    const dot = name.lastIndexOf('.');
    return STANDARD_NS.has(dot < 0 ? '' : name.slice(0, dot)) ? name.slice(dot + 1) : null;
  };
  const CONSTANTS = { pi: '\\pi', goldenRatio: '\\varphi', eulerMascheroniConstant: '\\gamma' };
  const FUNCTIONS = Object.fromEntries([
    ...['exp', 'log', 'sin', 'cos', 'tan', 'arcsin', 'arccos', 'arctan', 'sinh', 'cosh', 'tanh', 'arg', 'det', 'gcd', 'min', 'max'].map((f) => [f, '\\' + f]),
    ...['arsinh', 'arcosh', 'artanh', 'lcm'].map((f) => [f, `\\operatorname{${f}}`]),
    ['sqrt', '\\sqrt{\\cdot}'], ['abs', '\\lvert \\cdot \\rvert'],
  ]);
  // The same names applied to their arguments, where the notation wraps the argument.
  const ONE_ARGUMENT = { sqrt: (a) => `\\sqrt{${a}}`, abs: (a) => `\\lvert ${a} \\rvert` };
  const TWO_ARGUMENTS = {
    choose: (a, b) => `\\binom{${a}}{${b}}`,
    gcd: (a, b) => `\\gcd\\left(${a}, ${b}\\right)`, lcm: (a, b) => `\\operatorname{lcm}\\left(${a}, ${b}\\right)`,
    min: (a, b) => `\\min\\left(${a}, ${b}\\right)`, max: (a, b) => `\\max\\left(${a}, ${b}\\right)`,
  };
  const PARTS = { re: '\\operatorname{Re}', im: '\\operatorname{Im}' };

  // Spaces every mathematician writes with a symbol. `Real.Angle` is the reals modulo 2π.
  const SPACES = {
    Nat: '\\mathbb{N}', Int: '\\mathbb{Z}', Rat: '\\mathbb{Q}', Real: '\\mathbb{R}', Complex: '\\mathbb{C}',
    NNReal: '\\mathbb{R}_{\\ge 0}', NNRat: '\\mathbb{Q}_{\\ge 0}', ENNReal: '[0, \\infty]', EReal: '[-\\infty, +\\infty]',
    'Real.Angle': '\\mathbb{R}/2\\pi\\mathbb{Z}', UnitAddCircle: '\\mathbb{R}/\\mathbb{Z}', Circle: '\\mathbb{S}^{1}',
    GaussianInt: '\\mathbb{Z}[i]',
  };
  // The same for spaces built from something: `ZMod n` is ℤ/nℤ.
  const SPACES_OF = {
    Set: [1, (a) => `\\mathcal{P}\\left(${a}\\right)`], Finset: [1, (a) => `\\mathcal{P}_{\\mathrm{fin}}\\left(${a}\\right)`],
    Polynomial: [1, (r) => `${r}[X]`],
    ZMod: [1, (n) => `\\mathbb{Z}/${n}\\mathbb{Z}`], AddCircle: [1, (t) => `\\mathbb{R}/${t}\\mathbb{Z}`],
    Padic: [1, (p) => `\\mathbb{Q}_{${p}}`], PadicInt: [1, (p) => `\\mathbb{Z}_{${p}}`],
    'Equiv.Perm': [1, (a) => `\\operatorname{Sym}\\left(${a}\\right)`],
    Matrix: [3, (m, n, r) => `\\mathrm{M}_{${m} \\times ${n}}\\left(${r}\\right)`],
  };

  function ident(name) {
    if (name === '𝕜') return '\\Bbbk';
    if (name.length > 1 && name.endsWith('ˣ')) return `${ident(name.slice(0, -1))}^{\\times}`; // `Rˣ`: the group of units of R
    if (Object.hasOwn(SPACES, name)) return SPACES[name];
    if (name === 'Angle' && home === 'Real') return SPACES['Real.Angle']; // as written inside `namespace Real`
    if (name === 'Complex.I' || (name === 'I' && complex)) return 'i';
    if (name === 'rexp' || name === 'cexp') return '\\exp'; // Mathlib's short names for the real and complex exponential
    const known = standard(name);
    if (known && Object.hasOwn(CONSTANTS, known)) return CONSTANTS[known];
    if (known && Object.hasOwn(FUNCTIONS, known)) return FUNCTIONS[known];
    // `z.re`, `z.im`: the real and imaginary part of a variable.
    const part = /^([\p{L}][\p{L}\p{Nd}_'\u2080-\u2089]*)\.(re|im)$/u.exec(name);
    if (part) return `${PARTS[part[2]]}\\left(${ident(part[1])}\\right)`;
    // Script capitals (𝓝 neighbourhoods, 𝓤 uniformity, 𝓟 principal filter …) have their own alphabet in LaTeX.
    const script = /^[\u{1D4D0}-\u{1D4E9}]$/u.test(name) ? name.codePointAt(0) - 0x1D4D0 : -1;
    if (script >= 0) return `\\mathcal{${String.fromCharCode(65 + script)}}`;
    let m = /^([A-Za-z])(\d*)([\u2080-\u2089]*)('*)$/.exec(name);
    if (m) return m[1] + (m[2] || m[3] ? `_{${m[2]}${unsub(m[3])}}` : '') + m[4];
    m = /^(\p{Script=Greek})([\u2080-\u2089]*)('*)$/u.exec(name);
    if (m && GREEK[m[1]]) return `\\${GREEK[m[1]]}` + (m[2] ? `_{${unsub(m[2])}}` : '') + m[3];
    m = /^(.*?)([\u2080-\u2089]*)$/.exec(name);
    const body = unsub(m[1]).replace(/[_#%&${}]/g, (c) => '\\' + c).replace(/\^/g, '\\hat{}').replace(/~/g, '\\sim ');
    return `\\mathrm{${body}}` + (m[2] ? `_{${unsub(m[2])}}` : '');
  }

  // Lean can print each bound variable with its type, in brackets: `∃ (n : ℤ), …`,
  // `fun (x : ℝ) => …`, `⋃ (i : ι), …`. A quantifier is read as "∃ n : ℤ, …" (one
  // quantifier per bracket, which says the same); for the others the type is left out.
  const QUANTIFIER = /^(∃!|∃|∀)(?![ᶠ\p{L}\p{N}_])/u;
  const BINDER = /^(fun|λ|∀ᶠ|∃ᶠ|[⋃⋂⨆⨅∑∏∫∮]'?)(?![\p{L}\p{N}_])/u;
  function typedGroups(src, from) {
    const groups = [];
    let i = from;
    for (;;) {
      let j = i;
      while (src[j] === ' ') j++;
      if (src[j] !== '(') break;
      let depth = 0, k = j, colon = -1;
      for (; k < src.length; k++) {
        if ('([{⟨'.includes(src[k])) depth++;
        else if (')]}⟩'.includes(src[k])) { depth--; if (depth === 0) break; }
        else if (depth === 1 && colon < 0 && src[k] === ':' && src[k + 1] !== '=') colon = k;
      }
      const names = colon < 0 ? '' : src.slice(j + 1, colon).trim();
      if (k >= src.length || !/^[^\s()\[\]{}:,]+(\s+[^\s()\[\]{}:,]+)*$/.test(names)) break;
      groups.push({ names, type: src.slice(colon + 1, k).trim() });
      i = k + 1;
    }
    return { groups, end: i };
  }
  function plainBinders(src) {
    if (!src.includes('(')) return src;
    let out = '';
    for (let i = 0; i < src.length;) {
      const rest = src.slice(i);
      const boundary = i === 0 || !/[\p{L}\p{N}_.']/u.test(src[i - 1]);
      const q = boundary ? QUANTIFIER.exec(rest) : null, b = boundary && !q ? BINDER.exec(rest) : null;
      const word = q || b;
      if (!word) { out += src[i++]; continue; }
      const { groups, end } = typedGroups(src, i + word[0].length);
      if (!groups.length) { out += word[0]; i += word[0].length; continue; }
      // What a map applied to such a variable starts from (see introduceMaps). A name bound
      // twice with different types has no one type.
      if (q && boundTypes) for (const g of groups) for (const name of g.names.split(/\s+/)) {
        boundTypes.set(name, boundTypes.has(name) && boundTypes.get(name) !== g.type ? undefined : g.type);
      }
      if (q) out += groups.map((g, n) => `${q[0]} ${g.names} : ${plainBinders(g.type)}${n < groups.length - 1 ? ', ' : ''}`).join('');
      else out += `${b[0]} ${groups.map((g) => g.names).join(' ')}`;
      i = end;
    }
    return out;
  }

  function lex(given) {
    const src = plainBinders(String(given));
    const out = [];
    let i = 0;
    scan: while (i < src.length) {
      const c = src[i];
      if (/\s/.test(c)) { i++; continue; }
      for (const m of MULTI) {
        if (src.startsWith(m, i)) { out.push({ t: 'sym', v: m }); i += m.length; continue scan; }
      }
      const arrow = ARROW.exec(src.slice(i, i + 4));
      if (arrow) { out.push({ t: 'sym', v: arrow[0] }); i += arrow[0].length; continue; }
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
      // `(…).im`: a projection written straight after a closing bracket belongs to that bracket.
      if (c === '.' && out.length && out[out.length - 1].t === 'close') {
        const field = /^\.(\d+|[\p{L}_][\p{L}\p{Nd}_'!?]*)/u.exec(src.slice(i, i + 80));
        if (field) { out.push({ t: 'proj', v: field[1] }); i += field[0].length; continue; }
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
  // Norm bars ‖…‖ have no separate opening and closing sign: a bar closes the norm it is in
  // when it follows something complete (a name, a number, a bracket), and opens one otherwise.
  function nest(tokens) {
    try { return nestWith(tokens, true); } catch { return nestWith(tokens, false); } // bars that do not pair up stay as signs
  }
  // `√x`, `√(x + 1)`: the root sign and the term after it become one term, so that it can
  // be an argument, a factor or a denominator like any bracket. The same for a coercion `↑x`.
  function roots(items) {
    const out = [];
    for (let i = 0; i < items.length; i++) {
      const next = items[i + 1];
      const coverable = next && (next.t === 'id' || next.t === 'num' || next.t === 'group' || (next.t === 'sym' && next.v in ATOMS));
      if (items[i].t === 'sym' && (items[i].v === '√' || items[i].v === '↑') && coverable) out.push({ t: 'group', open: items[i].v, items: [items[++i]] });
      else out.push(items[i]);
    }
    return out;
  }
  function nestWith(tokens, pairNorms) {
    let i = 0;
    const complete = (n) => !!n && (n.t === 'id' || n.t === 'num' || n.t === 'group' || n.t === 'sup' || (n.t === 'sym' && n.v in ATOMS));
    const seq = (closer) => {
      const items = [];
      while (i < tokens.length) {
        const tok = tokens[i++];
        if (pairNorms && tok.t === 'sym' && tok.v === '‖') {
          if (closer === '‖' && complete(items[items.length - 1])) return roots(items);
          items.push({ t: 'group', open: '‖', items: seq('‖') });
          continue;
        }
        if (tok.t === 'close') {
          if (tok.v !== closer) throw new Error('unbalanced brackets');
          return roots(items);
        }
        if (tok.t === 'open') items.push({ t: 'group', open: tok.v, items: seq(CLOSER[tok.v]) });
        else if (tok.t === 'proj') {
          const last = items[items.length - 1]; // the lexer only emits one after a closing bracket
          if (last && last.t === 'group') (last.proj = last.proj || []).push(tok.v);
        } else items.push(tok);
      }
      if (closer) throw new Error('unbalanced brackets');
      return roots(items);
    };
    return roots(seq(null));
  }

  // `x : T` reads "x in T" when T is a collection of values: not a function type, not a universe.
  const isUniverse = (n) => n && ((n.t === 'id' && /^(Type|Sort|Prop)$/.test(n.v)) || n.v === 'Type*' || n.v === 'Sort*');
  const isArrow = (n) => n.t === 'sym' && (n.v === '→' || n.v === '->' || n.v === '↪' || n.v === '≃' || Object.hasOwn(MAPS, n.v));
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
  const isSym = (n, v) => !!n && n.t === 'sym' && n.v === v;
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
  // Set while converting a statement from the Complex namespace, where a bare `I` is the imaginary unit.
  let complex = false;
  // The namespace of the statement being converted when it fixes which number system a bare
  // `cos` or `exp` lives in: 'Real', 'Complex', 'NNReal', or '' when it does not.
  let home = '';
  // Set while converting with French / Belgian conventions: the angle ABC under a hat,
  // open interval ends as outward brackets, slanted ≤ and ≥.
  let french = false;
  const FRENCH_OPS = { '≤': '\\leqslant', '<=': '\\leqslant', '≥': '\\geqslant', '>=': '\\geqslant' };
  // Interval constructors: [left bracket, right bracket] as [international, French] pairs,
  // and which ends are bounded ('ab' both, 'a' left only, 'b' right only).
  const INTERVALS = {
    Icc: ['[', ']', 'ab'], Ico: ['[', ')', 'ab'], Ioc: ['(', ']', 'ab'], Ioo: ['(', ')', 'ab'],
    Ici: ['[', ')', 'a'], Ioi: ['(', ')', 'a'], Iic: ['(', ']', 'b'], Iio: ['(', ')', 'b'],
  };
  const bracket = (b) => (!french ? b : b === '(' ? ']' : b === ')' ? '[' : b);
  const isName = (n) => n && n.t === 'id' && !n.v.includes('.');

  // A coercion carries an element of one type into another: a real number regarded as a
  // complex one. Mathematics leaves it unwritten; Lean writes `↑x`. It is shown as a map
  // named ι, since leaving it out can turn a statement about the map into `x = x`.
  // `coercions`, while a statement is being converted, records each target type with the
  // plain variables the map was applied to; `iotaPlain` drops the subscript when there is
  // only one map to speak of.
  let coercions = null, iotaPlain = false, boundTypes = null;
  let eraseCasts = false; // while testing for a cast rule: write x for ι(x)
  function iota(target, arg) {
    if (coercions) {
      const seen = coercions.get(target) || { vars: new Set() };
      if (arg && arg.t === 'id' && !arg.v.includes('.')) seen.vars.add(arg.v);
      coercions.set(target, seen);
    }
    return iotaPlain || !target ? '\\iota' : `\\iota_{${target}}`;
  }

  // `binder` is true while rendering the inside of a quantifier's "(x : T)".
  function render(items, inSet, binder, info) {
    items = mergeChains(mergePowers(items));
    let quantified = false; // between a quantifier and its comma
    const out = []; // { s, atom }
    const atom = (s, bare) => out.push({ s, atom: true, bare }); // `bare`: the same thing without its own brackets
    const isOperand = (n) => isTerm(n) || (!!n && n.t === 'sym' && n.v in ATOMS);
    const POSTFIX = new Set(['^', '⁻¹', "⁻¹'", 'ᶜ']);
    const op = (s) => out.push({ s, atom: false });
    const join = (list) => list.map((e, k) => (k ? (list[k - 1].atom && e.atom ? '\\,' : ' ') : '') + e.s).join('').replace(/ ,\\;/g, ',\\;');
    // The operand of a prefix or postfix operator, without its own parentheses.
    // `(↑x : ℂ)` is a cast, not a bracketed expression: its brackets belong to it.
    const isCast = (node) => node.t === 'group' && node.open === '(' && node.items[0]?.t === 'group' && node.items[0].open === '↑' && isSym(node.items[1], ':');
    const inner = (node) => (!node ? '{}' : node.t === 'group' && node.open === '(' && !isCast(node) ? render(node.items) : render([node]));
    // In Lean `f x ^ 2` is `(f x) ^ 2`: a postfix applies to the whole application before it.
    const postfix = (s) => {
      let start = out.length;
      while (start > 0 && out[start - 1].atom) start--;
      const run = out.splice(start);
      if (!run.length) return atom('{}' + s);
      // A second superscript on the same base needs brackets: (x⁻¹)³, not x⁻¹³.
      const base = run.length > 1 || run[0].raised ? `\\left(${join(run)}\\right)` : run[0].s;
      atom(base + s);
      out[out.length - 1].raised = s.startsWith('^');
    };
    // `a / b` as a fraction. The numerator is the application just before the slash, the
    // denominator the application just after; if a power follows, it belongs to the last
    // factor only and the division is left as written. Returns the index of the last item
    // used, or 0 when no fraction was made.
    const fraction = (i) => {
      let start = out.length;
      while (start > 0 && out[start - 1].atom) start--;
      let end = i + 1;
      while (isOperand(items[end])) end++;
      const after = items[end];
      if (start === out.length || end === i + 1 || (after && (after.t === 'sup' || (after.t === 'sym' && POSTFIX.has(after.v))))) return 0;
      const run = out.splice(start);
      const top = run.length === 1 && run[0].bare !== undefined ? run[0].bare : join(run);
      const bottom = end === i + 2 ? inner(items[i + 1]) : render(items.slice(i + 1, end));
      atom(`\\frac{${top}}{${bottom}}`);
      return end - 1;
    };
    let used = 0;
    // An argument of a predicate, as a formula: brackets are kept unless they hold one term.
    const argument = (node) => {
      if (node.t !== 'group' || node.open !== '(' || node.proj || isCast(node)) return render([node]);
      const seen = {};
      const body = render(node.items, false, false, seen);
      return seen.single ? body : `\\left(${body}\\right)`;
    };
    const say = (text, args) => text.split(/(\{\d\}|⟦[^⟧]*⟧)/).filter(Boolean).map((piece) => (
      /^\{\d\}$/.test(piece) ? args[+piece[1]]
        : piece[0] === '⟦' ? piece.slice(1, -1).replace(/\{(\d)\}/g, (_, k) => args[+k])
        : `\\text{${piece}}`)).join(' ');
    // Where a filter is a familiar place: +∞, −∞, or a point (its neighbourhood filter 𝓝 a).
    const place = (node) => {
      if (node.t === 'id' && /^(Filter\.)?atTop$/.test(node.v)) return '+\\infty';
      if (node.t === 'id' && /^(Filter\.)?atBot$/.test(node.v)) return '-\\infty';
      if (node.t !== 'group' || node.open !== '(' || node.items[0]?.t !== 'id' || !/^(𝓝|nhds)$/.test(node.items[0].v)) return null;
      const point = (at) => (at.t === 'group' && at.open === '(' ? render(at.items) : render([at]));
      if (node.items.length === 2) return point(node.items[1]);
      // `𝓝[<] a`, `𝓝[>] a`: from the left, from the right, written a⁻ and a⁺. `𝓝[≠] a` leaves
      // the point out, and `𝓝[s] a` approaches it inside a set.
      const [, how, at] = node.items;
      if (node.items.length !== 3 || how.t !== 'group' || how.open !== '[') return null;
      const side = how.items.length === 1 && how.items[0].t === 'sym' ? { '<': '-', '>': '+' }[how.items[0].v] : null;
      if (side) return `${at.t === 'id' || at.t === 'num' ? render([at]) : `\\left(${point(at)}\\right)`}^{${side}}`;
      if (how.items.length === 1 && isSym(how.items[0], '≠')) return `${point(at)} \\text{ (excluded)}`;
      if (how.items.some((n) => n.t === 'sym' && /^[<>≤≥≠]$/.test(n.v))) return null; // `𝓝[≤] a` and the like: no short form
      return `${point(at)} \\text{ within } ${render(how.items)}`;
    };
    // `cos`, `exp`, `√` … named as a function, with where it goes from and to: Mathlib has a
    // real and a complex version of each, and a statement about the function should say which.
    const CARRIER = { Real: '\\mathbb{R}', Complex: '\\mathbb{C}', NNReal: '\\mathbb{R}_{\\ge 0}' };
    const TO_REALS = new Set(['Complex.arg', 'Complex.abs']);
    const ONE_VARIABLE = new Set(['exp', 'log', 'sin', 'cos', 'tan', 'arcsin', 'arccos', 'arctan', 'sinh', 'cosh', 'tanh', 'arsinh', 'arcosh', 'artanh', 'arg', 'sqrt', 'abs']);
    const typed = (node) => {
      if (node.t !== 'id') return null;
      const short = { rexp: 'Real.exp', cexp: 'Complex.exp' }[node.v];
      const full = short || (node.v.includes('.') ? node.v : home ? `${home}.${node.v}` : node.v);
      const dot = full.lastIndexOf('.');
      const from = CARRIER[full.slice(0, dot)];
      if (dot < 0 || !from || !ONE_VARIABLE.has(full.slice(dot + 1))) return null;
      return `${ident(full)} : ${from} \\to ${TO_REALS.has(full) ? CARRIER.Real : from}`;
    };
    // `ContinuousOn f s` as "f is continuous on s", `s.Nonempty` as "s is nonempty", and
    // `Tendsto f atTop (𝓝 a)` as a limit. Returns the index after the last item used, or 0 when
    // items[i] is not a known predicate applied to the right number of arguments. (The index
    // returned is the one after the last item used, since a predicate may use none but its own.)
    const predicate = (i) => {
      const name = items[i].v;
      const dotted = /^([\p{L}][\p{L}\p{Nd}_'₀-₉]*)\.([A-Z][A-Za-z]*)$/u.exec(name);
      const entry = Phrases.predicate(name) || (dotted && Phrases.predicate(dotted[2], true));
      const limit = /^(Filter\.)?Tendsto$/.test(name);
      if (!entry && !limit) return 0;
      let end = i + 1;
      while (isOperand(items[end])) end++;
      const given = items.slice(i + 1, end);
      if (limit) {
        if (given.length !== 3) return 0;
        const from = place(given[1]), to = place(given[2]);
        // "f tends to a at +∞" when the filters are familiar places; "along l" for one that is not.
        // In words, so that the arrow of a function's own "ℝ → ℝ" is the only arrow in sight.
        const f = typed(given[0]) || argument(given[0]);
        atom(`${f} \\text{ tends to } ${to ?? argument(given[2])} \\text{ ${from ? 'at' : 'along'} } ${from ?? argument(given[1])}`);
        return end;
      }
      const args = [...(Phrases.predicate(name) ? [] : [ident(dotted[1])]), ...given.map((a) => typed(a) || argument(a))];
      if (args.length < entry.arity || args.length > entry.arity + entry.extra) return 0;
      atom(say(entry.text, args));
      return end;
    };
    // `f '' s` is the image of the set s under f, and `f ⁻¹' s` its preimage: f(s) and f⁻¹(s).
    // The function is the application just before the sign, the set the one just after.
    // Returns the index of the last item used, or 0 when either side is missing.
    const image = (i, exponent) => {
      let start = out.length;
      while (start > 0 && out[start - 1].atom) start--;
      let end = i + 1;
      while (isOperand(items[end])) end++;
      if (start === out.length || end === i + 1) return 0;
      const run = out.splice(start);
      const f = run.length > 1 ? `\\left(${join(run)}\\right)` : run[0].s;
      const set = end === i + 2 ? inner(items[i + 1]) : render(items.slice(i + 1, end));
      atom(`${f}${exponent}\\left(${set}\\right)`);
      return end - 1;
    };
    // `Set.Icc a b` as [a, b], and the other seven interval shapes. Returns the index of the
    // last item used, or 0 when items[i] is not an interval applied to its bounds.
    const interval = (i) => {
      const shape = INTERVALS[items[i].v.replace(/^Set\./, '')];
      if (!shape) return 0;
      const count = shape[2].length;
      if (![...Array(count)].every((_, k) => isOperand(items[i + 1 + k])) || isOperand(items[i + 1 + count])) return 0; // a bound may be a sign such as π
      const a = shape[2].includes('a') ? inner(items[i + 1]) : '-\\infty';
      const b = shape[2].includes('b') ? inner(items[i + count]) : '+\\infty';
      atom(`\\left${bracket(shape[0])}${a}, ${b}\\right${bracket(shape[1])}`);
      return i + count;
    };
    // `(…).im`, `(…).1`, `(…).tan`: what is written after a bracket with a dot. A standard
    // function or the real and imaginary part is applied the usual way round, tan(…); any
    // other field stays attached to its bracket.
    const project = (node) => {
      if (!node.proj) return;
      const last = out[out.length - 1];
      const only = node.proj.length === 1 ? node.proj[0] : null;
      const wrap = only && (Object.hasOwn(PARTS, only) ? PARTS[only] : Object.hasOwn(FUNCTIONS, only) && !FUNCTIONS[only].includes('cdot') ? FUNCTIONS[only] : null);
      if (wrap) last.s = `${wrap}\\left(${last.bare ?? last.s}\\right)`;
      else last.s += node.proj.map((f) => '.' + (/^\d+$/.test(f) ? f : `\\mathrm{${f.replace(/_/g, '\\_')}}`)).join('');
      last.bare = undefined;
    };
    for (let i = 0; i < items.length; i++) {
      const node = items[i];
      if (node.t === 'group' && node.open === '[' && node.items.length === 1 && node.items[0].t === 'id' && node.items[0].v === 'X' && out.length && out[out.length - 1].atom) {
        out[out.length - 1].s += '[X]'; // the polynomial ring over what stands before
        out[out.length - 1].bare = undefined;
      } else if (node.t === 'group' && node.open === '↑') {
        const said = iota('', node.items[0]);
        if (eraseCasts) atom(`\\left(${inner(node.items[0])}\\right)`);
        else atom(`${said}\\left(${inner(node.items[0])}\\right)`); // `↑x` with no type written
      } else if (isCast(node)) {
        // `(↑x : ℂ)`: x carried into ℂ by the canonical map.
        const arg = node.items[0].items[0];
        const inside = inner(arg);
        const said = iota(render(node.items.slice(2)), arg);
        atom(eraseCasts ? `\\left(${inside}\\right)` : `${said}\\left(${inside}\\right)`);
        project(node);
      } else if (node.t === 'group') {
        const body = render(node.items, node.open === '{', quantified && node.open !== '⟨');
        if (node.open === '(') atom(`\\left(${body}\\right)`, body);
        else if (node.open === '[') atom(`\\left[${body}\\right]`);
        else if (node.open === '⟨') atom(`\\langle ${body} \\rangle`);
        else if (node.open === '‖') atom(`\\| ${body} \\|`);
        else if (node.open === '√') atom(`\\sqrt{${inner(node.items[0])}}`);
        else if (node.open === '⟪') {
          // An inner product ⟪x, y⟫, optionally tagged with its scalar field: ⟪x, y⟫_ℝ.
          const tagged = items[i + 1] && items[i + 1].t === 'sym' && items[i + 1].v === '_' && isOperand(items[i + 2]);
          atom(`\\langle ${body.replace(/,\\;/g, ',')} \\rangle` + (tagged ? `_{${inner(items[i + 2])}}` : ''));
          if (tagged) i += 2;
        }
        else atom(`\\{ ${body} \\}`);
        project(node);
      } else if (node.t === 'num') atom(node.v);
      else if (node.t === 'sup') postfix(`^{${node.v}}`);
      else if (node.t === 'id') {
        if (node.v === 'fun' || node.v === 'λ') continue;
        if (node.v in WORDS) op(WORDS[node.v]);
        else if (Object.hasOwn(SPACES_OF, node.v) && [...Array(SPACES_OF[node.v][0])].every((_, k) => isOperand(items[i + 1 + k])) && !isOperand(items[i + 1 + SPACES_OF[node.v][0]])) {
          const [count, write] = SPACES_OF[node.v];
          atom(write(...items.slice(i + 1, i + 1 + count).map(inner)));
          i += count;
        } else if ((used = predicate(i))) i = used - 1;
        else if (standard(node.v) === 'factorial' && isTerm(items[i + 1]) && !isTerm(items[i + 2])) {
          atom(`${render([items[++i]])}!`);
        } else if (Object.hasOwn(ONE_ARGUMENT, standard(node.v) || '') && isTerm(items[i + 1]) && !isTerm(items[i + 2])) {
          atom(ONE_ARGUMENT[standard(node.v)](inner(items[++i])));
        } else if (Object.hasOwn(TWO_ARGUMENTS, standard(node.v) || '') && isTerm(items[i + 1]) && isTerm(items[i + 2]) && !isTerm(items[i + 3])) {
          atom(TWO_ARGUMENTS[standard(node.v)](inner(items[i + 1]), inner(items[i + 2])));
          i += 2;
        } else if (node.v === 'dist' && isTerm(items[i + 1]) && isTerm(items[i + 2]) && !isTerm(items[i + 3])) {
          const a = items[i + 1], b = items[i + 2];
          if (geometry && isName(a) && isName(b)) atom(`\\lvert ${inner(a)} ${inner(b)} \\rvert`);
          else atom(`d\\left(${inner(a)}, ${inner(b)}\\right)`);
          i += 2;
        } else if ((used = interval(i))) i = used;
        else if ((node.v === 'angle' || node.v === 'InnerProductGeometry.angle') && isTerm(items[i + 1]) && isTerm(items[i + 2]) && !isTerm(items[i + 3])) {
          atom(`\\angle\\left(${inner(items[i + 1])}, ${inner(items[i + 2])}\\right)`); // the angle between two vectors
          i += 2;
        } else atom(ident(node.v));
      } else {
        const v = node.v;
        if ((v === '∠' || v === '∡') && [1, 2, 3].every((k) => isTerm(items[i + k])) && !isTerm(items[i + 4])) {
          // The angle at the middle point: "∠ABC" for named points, bracketed otherwise.
          const points = items.slice(i + 1, i + 4);
          if (!points.every(isName)) atom(`${OPS[v]}\\left(${points.map(inner).join(', ')}\\right)`);
          else if (french && v === '∠') atom(`\\widehat{${points.map(inner).join(' ')}}`);
          else atom(`${OPS[v]} ${points.map(inner).join(' ')}`);
          i += 3;
        } else if (v === '/' && (used = fraction(i))) i = used;
        else if (v === '√') atom(`\\sqrt{${inner(items[++i])}}`);
        else if (v === '^') {
          // Powers associate to the right in Lean: x ^ p ^ n is x ^ (p ^ n).
          const tower = (k) => (isSym(items[k + 1], '^') && items[k + 2]
            ? (([rest, last]) => [`${inner(items[k])}^{${rest}}`, last])(tower(k + 2))
            : [inner(items[k]), k]);
          const [exponent, last] = tower(i + 1);
          postfix(`^{${exponent}}`);
          i = last;
        }
        else if ((v === "''" || v === "⁻¹'") && (used = image(i, v === "''" ? '' : '^{-1}'))) i = used;
        else if (v === '⁻¹' || v === "⁻¹'") postfix('^{-1}'); // inverse; a preimage sign with nothing after it
        else if (Object.hasOwn(MAPS, v)) {
          const [label, scalars, iso] = MAPS[v];
          const over = scalars && items[i + 1]?.t === 'group' && items[i + 1].open === '[' ? render(items[++i].items) : '';
          const what = over ? `${over}\\text{-${label}}` : `\\text{${label}}`;
          op(iso ? `\\xrightarrow[${what}]{\\sim}` : `\\xrightarrow{${what}}`);
        }
        else if (v === 'ᶜ') postfix('^{c}');
        else if (v === 'ˣ') postfix('^{\\times}'); // the group of units
        else if ((v === 'ℚ' || v === 'ℤ') && isSym(items[i + 1], '_') && items[i + 2]?.t === 'group' && items[i + 2].open === '[') {
          atom(`${ATOMS[v]}_{${render(items[i + 2].items)}}`); // the p-adic numbers and integers
          i += 2;
        }
        else if (v === '!' && out.length && out[out.length - 1].atom) out[out.length - 1].s += '!'; // factorial: `n !`, `(n + 1)!`
        else if (v in BIGOPS && items.slice(i + 1).some((n) => n.t === 'sym' && n.v === ',')) {
          const end = items.findIndex((n, k) => k > i && n.t === 'sym' && n.v === ',');
          op(`${BIGOPS[v]}_{${render(items.slice(i + 1, end))}}`);
          i = end;
        } else if (v === '↑') {
          atom('\\uparrow'); // the coercion function on its own, `(↑)`; applied, it was made a term above
        } else if (v === '⇑' || v === '↥') {
          if (i + 1 >= items.length) atom('\\uparrow'); // otherwise left out: `⇑f x` is just f x
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
        else if (v in OPS) op((french && FRENCH_OPS[v]) || OPS[v]);
        else if (v === '{' || v === '}') op('\\' + v);
        else op(v);
      }
    }
    if (info) info.single = out.length === 1 && out[0].atom; // the caller may drop brackets around one term
    return join(out);
  }

  // One Lean expression as LaTeX math. Throws on unbalanced brackets.
  function expr(src, options) {
    const before = french; // toLatex calls this too, and its choice of notation must survive
    if (options) french = options.notation === 'fr';
    try { return render(nest(lex(String(src)))); } finally { french = before; }
  }

  const RELATION = /[=≠≤<≥>∈∉⊆⊂↔∣∀∃¬∧∨≡]/;
  const NUMBER_SET = /^([ℕℤℚℝℂ]|[ℝℚ]≥0∞?)$/;
  const KINDS = { theorem: 'Theorem', lemma: 'Lemma', axiom: 'Axiom', def: 'Definition', abbrev: 'Abbreviation', opaque: 'Definition', instance: 'Instance' };
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
      if (!(open in CLOSER) || open === '⟨' || open === '⟪') break;
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

  // "lhs := body" for an abbreviation whose body is a formula. A body that is a program
  // (tactics, pattern matching, a structure being filled in, local definitions) or simply
  // long is not one, and gives null. `body` is the source text from ":=" on.
  const NOT_A_FORMULA = /(^|[\s(])(by|match|where|do|calc|show|from|let|letI|have|haveI|sorry)\b|:=|⟨|@\[|^\s*\||\n\s*\|/;
  function shorthandFormula(lhs, body) {
    if (typeof body !== 'string' || !/^\s*:=/.test(body)) return null;
    const rhs = body.replace(/^\s*:=/, '').trim();
    if (!rhs || rhs.length > 240 || rhs.split('\n').length > 5 || NOT_A_FORMULA.test(rhs)) return null;
    try { return `${expr(lhs)} := ${expr(rhs.replace(/\s+/g, ' '))}`; } catch { return null; }
  }

  // toLatex returns { kind, parts, source, thesis } or null when the statement is not one this can render.
  // `thesis` is the formula for a node: the conclusion alone; for a definition its signature;
  // for an abbreviation what it stands for, when `options.body` holds a body that is a formula.
  // `parts` alternate prose ({ text }) and formulas ({ math, display? }); `source` is LaTeX.
  // `context` is the binder text of the `variable` commands in scope, if known.
  function toLatex(statement, fullName, context, options) {
    coercions = new Map();
    iotaPlain = false;
    boundTypes = new Map();
    try {
      let result = convert(statement, fullName, context, options);
      // `thesisAlone`: the conclusion for use without the sentence that introduces a map, so
      // each map says where it lands (ι_ℝ).
      if (!result || !coercions.size) return result && { ...result, thesisAlone: result.thesis };
      const maps = coercions, types = boundTypes, thesisAlone = result.thesis;
      if (maps.size === 1) { // one map only: plain ι, with no subscript
        iotaPlain = true;
        coercions = new Map();
        result = convert(statement, fullName, context, options);
      }
      return { ...introduceMaps(result, maps, types, options), thesisAlone };
    } finally {
      coercions = null;
      iotaPlain = false;
      boundTypes = null;
    }
  }

  // Adds "Let ι : ℝ → ℂ be the canonical map" before the formula. Where a map starts is known
  // when it was applied to plain variables that all have the same stated type.
  function introduceMaps(result, maps, types, options) {
    const startOf = (seen) => {
      const from = new Set([...seen.vars].map((v) => types.get(v)));
      return seen.vars.size && from.size === 1 && !from.has(undefined) ? expr([...from][0], options) : null;
    };
    const body = result.parts.slice(0, -1).map((p) => ({ ...p })), display = result.parts[result.parts.length - 1];
    let closing = '. Then';
    const last = body[body.length - 1];
    const ends = last && 'text' in last ? /\. (Then|Write)$/.exec(last.text) : null;
    if (ends) {
      closing = '. ' + ends[1];
      last.text = last.text.slice(0, ends.index);
      if (!last.text) body.pop();
    }
    const text = (t) => {
      const end = body[body.length - 1];
      if (end && 'text' in end) end.text += t;
      else body.push({ text: t });
    };
    text(body.length ? '. Let ' : 'Let ');
    if (maps.size === 1) {
      const [[target, seen]] = [...maps];
      const start = startOf(seen);
      if (target && start) { body.push({ math: `\\iota : ${start} \\to ${target}` }); text(' be the canonical map'); }
      else if (target) { body.push({ math: '\\iota' }); text(' be the canonical map into '); body.push({ math: target }); }
      else if (start) { body.push({ math: '\\iota' }); text(' be the canonical map from '); body.push({ math: start }); }
      else { body.push({ math: '\\iota' }); text(' be the canonical map'); }
    } else {
      const targets = [...maps.keys()].filter(Boolean);
      targets.forEach((target, k) => { if (k) text(', '); body.push({ math: `\\iota_{${target}}` }); });
      text(' be the canonical maps into ');
      targets.forEach((target, k) => { if (k) text(', '); body.push({ math: target }); });
    }
    text(closing);
    const lines = result.source.split('\n');
    const prose = body.map((p) => ('text' in p ? p.text : `$${p.math}$`)).join('');
    return { ...result, parts: [...body, display], source: [lines[0], prose, lines[lines.length - 2], lines[lines.length - 1]].join('\n') };
  }

  // Whether a theorem is a cast rule: one that only moves a canonical map across an
  // operation, like ι(r/s) = ι(r)/ι(s) or "tan of the angle of x is tan x". The test needs
  // no convention: erase every cast, and see whether the two sides of the equation (or of
  // the equivalence) have become the same.
  // Typeset text split at a sign, at the top level only: outside every bracket and brace.
  function splitTex(text, sign) {
    const pieces = [];
    let depth = 0, start = 0;
    for (let i = 0; i < text.length; i++) {
      if (text.startsWith('\\left', i) || text[i] === '{') depth++;
      else if (text.startsWith('\\right', i) || text[i] === '}') depth--;
      else if (depth === 0 && text.startsWith(sign, i)) { pieces.push(text.slice(start, i)); start = i + sign.length; i = start - 1; }
    }
    return [...pieces, text.slice(start)];
  }
  // The two sides of a typeset conclusion that is an equivalence or an equation, as a
  // rewrite uses it: [left, right]. Null for anything else (an implication, a statement
  // about all x, an "or" of equations), where there are no two sides to speak of.
  function sides(thesis) {
    const text = String(thesis || '');
    if (/^\s*\\(forall|exists)\b/.test(text)) return null;
    const iff = splitTex(text, ' \\iff ');
    if (iff.length === 2) return iff.map((x) => x.trim());
    if (iff.length > 2) return null;
    if ([' \\to ', ' \\lor ', ' \\land ', '\\neg '].some((sign) => splitTex(text, sign).length > 1)) return null;
    const eq = splitTex(text, ' = ');
    return eq.length === 2 ? eq.map((x) => x.trim()) : null;
  }

  function castRule(statement, fullName, context, options) {
    coercions = new Map();
    iotaPlain = true;
    boundTypes = new Map();
    eraseCasts = true;
    try {
      const result = convert(statement, fullName, context, options);
      if (!result || !coercions.size || !/^(Theorem|Lemma)$/.test(result.kind)) return false;
      const split = splitTex;
      const bare = (text) => text.replace(/\\left|\\right|\\,|[(){}\s]/g, '');
      const whole = result.thesis;
      const sides = split(whole, ' \\iff ').length === 2 ? split(whole, ' \\iff ') : split(whole, ' = ');
      return sides.length === 2 && bare(sides[0]) !== '' && bare(sides[0]) === bare(sides[1]);
    } catch {
      return false;
    } finally {
      coercions = null;
      iotaPlain = false;
      boundTypes = null;
      eraseCasts = false;
    }
  }

  function convert(statement, fullName, context, options) {
    french = !!options && options.notation === 'fr';
    geometry = /^EuclideanGeometry\./.test(String(fullName || ''));
    complex = /^Complex\./.test(String(fullName || ''));
    home = (/^(Real|Complex|NNReal)\./.exec(String(fullName || '')) || [])[1] || '';
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
      const proposition = kind === 'Theorem' || kind === 'Lemma' || kind === 'Axiom'; // states a fact, as opposed to defining a thing
      // An abbreviation is a short name for an expression, so that expression is what it says.
      // (A definition's body is how it is computed, and is not taken for its meaning.)
      const names = binders.filter((b) => b.open === '(').flatMap((b) => {
        const colon = topLevel(b.body, ':');
        return (colon < 0 ? b.body : b.body.slice(0, colon)).trim().split(/\s+/).filter(Boolean);
      });
      const shortName = declared ? declared[0].replace(/^_root_\./, '') : name;
      const shorthand = head[1] === 'abbrev' ? shorthandFormula([shortName, ...names].join(' '), options && options.body) : null;
      if (!conclusion && !shorthand) return null;
      // What a definition says is its signature: what it takes and what it gives. How it is
      // computed is its body, which is shown as source, like a proof.
      const args = binders.filter((b) => b.open === '(').flatMap((b) => {
        const colon = topLevel(b.body, ':');
        const type = colon < 0 ? '' : b.body.slice(colon + 1).split(':=')[0].trim();
        return (colon < 0 ? b.body : b.body.slice(0, colon)).trim().split(/\s+/).filter(Boolean).map((arg) => ({ arg, type }));
      });
      const written = declared ? declared[0].replace(/^_root_\./, '') : name;
      const result = conclusion ? `${memberOf(nest(lex(conclusion))) ? '\\in' : ':'} ${expr(conclusion)}` : '';
      // Focused: "Let x ∈ ℂ. Then arg x ∈ ℝ". In a node: "arg : ℂ → ℝ", or the applied form again
      // when an argument's type depends on an earlier argument and no product can be written.
      const applied = `${expr([written, ...args.map((a) => a.arg)].join(' '))} ${result}`;
      const dependent = args.some((a) => !a.type || mentioned(a.type).some((n) => args.some((o) => o.arg === n)));
      const domain = (type) => (hasTopLevel(type, /→/) ? `\\left(${expr(type)}\\right)` : expr(type));
      const signature = !args.length ? `${ident(written)} ${result}`
        : dependent ? applied
        : `${ident(written)} : ${args.map((a) => domain(a.type)).join(' \\times ')} \\to ${expr(conclusion || '')}`;

      const vars = [], insts = [], hyps = [];
      const subjects = [], about = new Map(), typeVars = new Set(); // what the typeclasses talk about
      const typed = new Set(); // names a binder has already given a type
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
        if (type && boundTypes) names.forEach((n) => boundTypes.set(n, type));
        if (!type) {
          // `variable (V)` after `{V : Type*}` only makes V an explicit argument: nothing new to introduce.
          const fresh = names.filter((n) => !typed.has(n));
          if (fresh.length) vars.push(fresh.map(ident).join(', '));
          fresh.forEach((n) => typed.add(n));
          continue;
        }
        names.forEach((n) => typed.add(n));
        if (/^(Type|Sort)\b/.test(type)) { names.forEach((n) => { typeVars.add(n); subject(n); }); continue; }
        // Hypotheses are usually called h, hx, h₁ … or given a descriptive name such as f_mble.
        const named = names.every((n) => /^h[\p{L}\p{N}_'₀-₉]*$/u.test(n) || n.includes('_')) && !NUMBER_SET.test(type) && !/^Prop\b/.test(type);
        // The ≥ in the names ℝ≥0 and ℝ≥0∞ is part of the name, not a relation.
        if (hasTopLevel(type.replace(/[ℝℚ]≥0∞?/g, 'ℝ'), RELATION) || named) hyps.push(expr(type));
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
      if (parts.length) text(shorthand ? '. Write' : '. Then');
      const shown = proposition ? expr(conclusion) : shorthand || applied;
      parts.push({ math: shown, display: true });

      const env = kind === 'Lemma' ? 'lemma' : proposition ? 'theorem' : 'definition';
      const prose = parts.slice(0, -1).map((p) => ('text' in p ? p.text : `$${p.math}$`)).join('');
      const source = [
        `\\begin{${env}}[\\texttt{${name.replace(/[_#%&${}]/g, (c) => '\\' + c)}}]`,
        ...(prose ? [prose] : []),
        `\\[ ${shown} \\]`,
        `\\end{${env}}`,
      ].join('\n');
      return { kind, parts, source, thesis: proposition ? shown : shorthand || signature };
    } catch {
      return null;
    } finally {
      geometry = false;
      complex = false;
      home = '';
      french = false;
    }
  }

  return { expr, toLatex, castRule, sides };
});
