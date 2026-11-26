// A phrasebook for Mathlib typeclasses: turns `[Field K] [LinearOrder K] …` into
// "K is a linearly ordered field". Classes not listed here are reported back as leftovers.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.LeanPhrases = factory();
})(this, function () {
  'use strict';

  // n: a noun ("field"); adj: goes before the noun ("compact"); post: goes after it
  // ("of characteristic zero"); be: a complete complement; hyp: really a hypothesis;
  // drop: computational bookkeeping with no mathematical content.
  // `scalar` marks classes whose first argument is a scalar field or ring.
  // `subj` is the index of the argument the class is about (default: the last).
  const n = (t, extra) => ({ c: 'n', t, ...extra });
  const adj = (t, extra) => ({ c: 'adj', t, ...extra });
  const post = (t, extra) => ({ c: 'post', t, ...extra });
  const DROP = { c: 'drop' };

  const PHRASES = {
    // algebra
    Semigroup: n('semigroup'), Monoid: n('monoid'), CommMonoid: n('commutative monoid'), Group: n('group'), CommGroup: n('abelian group'),
    AddSemigroup: n('additive semigroup'), AddMonoid: n('additive monoid'), AddCommMonoid: n('commutative additive monoid'),
    AddGroup: n('additive group'), AddCommGroup: n('abelian group'),
    Semiring: n('semiring'), CommSemiring: n('commutative semiring'), Ring: n('ring'), CommRing: n('commutative ring'),
    NonUnitalNonAssocSemiring: n('non-unital non-associative semiring'), NonUnitalNonAssocRing: n('non-unital non-associative ring'),
    NonUnitalSemiring: n('non-unital semiring'), NonUnitalRing: n('non-unital ring'), NonAssocSemiring: n('non-associative semiring'),
    NonAssocRing: n('non-associative ring'), NonUnitalCommRing: n('non-unital commutative ring'),
    DivisionRing: n('division ring'), Field: n('field'), Semifield: n('semifield'), EuclideanDomain: n('Euclidean domain'),
    IsDomain: n('domain'), IsDedekindDomain: n('Dedekind domain'), IsPrincipalIdealRing: n('principal ideal ring'),
    UniqueFactorizationMonoid: n('unique factorisation monoid'), NumberField: n('number field'),
    GroupWithZero: n('group with zero'), CommGroupWithZero: n('commutative group with zero'), MonoidWithZero: n('monoid with zero'),
    MulZeroClass: post('with a multiplication and a zero'), CancelCommMonoidWithZero: n('cancellative commutative monoid with zero'),
    NoZeroDivisors: post('without zero divisors'), Nontrivial: adj('nontrivial'), CharZero: post('of characteristic zero'),
    CharP: post('of characteristic {1}', { arity: 2, subj: 0 }), IsAlgClosed: adj('algebraically closed'),
    IsNoetherianRing: adj('Noetherian'), IsArtinianRing: adj('Artinian'), IsLocalRing: adj('local'), IsReduced: adj('reduced'),
    IsCyclic: adj('cyclic'), IsSimpleGroup: adj('simple'), IsIntegrallyClosed: adj('integrally closed'),
    Module: n('module', { scalar: true, plain: true }), Algebra: n('algebra', { scalar: true, plain: true }),
    LieRing: n('Lie ring'), LieAlgebra: n('Lie algebra', { scalar: true, plain: true }),
    FiniteDimensional: adj('finite-dimensional', { arity: 2 }), 'Module.Finite': adj('finitely generated', { arity: 2 }),
    'Module.Free': adj('free', { arity: 2 }), IsScalarTower: DROP, SMulCommClass: DROP,
    Zero: post('with a zero element'), One: post('with a unit element'), Add: post('with an addition'), Mul: post('with a multiplication'),
    Neg: post('with a negation'), Inv: post('with an inversion'), Star: post('with a star operation'), StarRing: post('with an involution'),
    // order
    Preorder: n('preordered set'), PartialOrder: n('partially ordered set'), LinearOrder: n('linearly ordered set'),
    Lattice: n('lattice'), DistribLattice: n('distributive lattice'), CompleteLattice: n('complete lattice'),
    SemilatticeSup: n('join-semilattice'), SemilatticeInf: n('meet-semilattice'), BooleanAlgebra: n('Boolean algebra'),
    ConditionallyCompleteLinearOrder: n('conditionally complete linear order'), CompleteLinearOrder: n('complete linear order'),
    OrderBot: post('with a least element'), OrderTop: post('with a greatest element'), BoundedOrder: post('with a least and a greatest element'),
    NoMaxOrder: post('with no greatest element'), NoMinOrder: post('with no least element'),
    DenselyOrdered: adj('densely ordered'), Archimedean: adj('Archimedean'), LocallyFiniteOrder: adj('locally finite'),
    IsStrictOrderedRing: n('strictly ordered ring'), IsOrderedRing: n('ordered ring'),
    LinearOrderedField: n('linearly ordered field'), LinearOrderedRing: n('linearly ordered ring'),
    LinearOrderedCommRing: n('linearly ordered commutative ring'), LinearOrderedSemiring: n('linearly ordered semiring'),
    OrderedSemiring: n('ordered semiring'), OrderedRing: n('ordered ring'),
    // topology
    TopologicalSpace: n('topological space'), MetricSpace: n('metric space'), PseudoMetricSpace: n('pseudometric space'),
    EMetricSpace: n('extended metric space'), PseudoEMetricSpace: n('extended pseudometric space'), UniformSpace: n('uniform space'),
    T0Space: adj('T₀'), T1Space: adj('T₁'), T2Space: adj('Hausdorff'), T3Space: adj('T₃'), RegularSpace: adj('regular'), NormalSpace: adj('normal'),
    T4Space: adj('T₄'), CompactSpace: adj('compact'), LocallyCompactSpace: adj('locally compact'), WeaklyLocallyCompactSpace: adj('locally compact'),
    ConnectedSpace: adj('connected'), PreconnectedSpace: adj('preconnected'), LocallyConnectedSpace: adj('locally connected'),
    TotallyDisconnectedSpace: adj('totally disconnected'), SeparableSpace: adj('separable'), 'TopologicalSpace.SeparableSpace': adj('separable'),
    SecondCountableTopology: adj('second-countable'), FirstCountableTopology: adj('first-countable'), CompleteSpace: adj('complete'),
    DiscreteTopology: adj('discrete'), ProperSpace: adj('proper'), PolishSpace: adj('Polish'), BaireSpace: adj('Baire'),
    SigmaCompactSpace: adj('σ-compact'), NoncompactSpace: adj('non-compact'),
    IsTopologicalGroup: n('topological group'), IsTopologicalAddGroup: n('topological additive group'), IsTopologicalRing: n('topological ring'),
    TopologicalGroup: n('topological group'), TopologicalAddGroup: n('topological additive group'), TopologicalRing: n('topological ring'),
    ContinuousAdd: post('with continuous addition'), ContinuousMul: post('with continuous multiplication'),
    ContinuousSMul: post('with continuous scalar multiplication', { arity: 2 }), ContinuousConstSMul: DROP,
    OrderTopology: post('with the order topology'), OrderClosedTopology: post('with an order-closed topology'),
    BorelSpace: post('with its Borel σ-algebra'), OpensMeasurableSpace: post('whose open sets are measurable'),
    // analysis
    NormedAddCommGroup: n('normed abelian group'), SeminormedAddCommGroup: n('seminormed abelian group'),
    NormedAddGroup: n('normed additive group'), SeminormedAddGroup: n('seminormed additive group'),
    NormedRing: n('normed ring'), NormedCommRing: n('normed commutative ring'), SeminormedRing: n('seminormed ring'),
    NormedField: n('normed field'), NontriviallyNormedField: n('nontrivially normed field'), DenselyNormedField: n('densely normed field'),
    NormedDivisionRing: n('normed division ring'),
    NormedSpace: n('normed space', { scalar: true }), InnerProductSpace: n('inner product space', { scalar: true }),
    NormedAlgebra: n('normed algebra', { scalar: true }),
    RCLike: { c: 'be', t: ['either ', { lean: 'ℝ' }, ' or ', { lean: 'ℂ' }] }, IsROrC: { c: 'be', t: ['either ', { lean: 'ℝ' }, ' or ', { lean: 'ℂ' }] },
    AddTorsor: n('affine space over {0}', { arity: 2 }), NormedAddTorsor: n('affine space over {0}', { arity: 2 }),
    // measure theory
    MeasurableSpace: n('measurable space'), MeasureSpace: n('measure space'), MeasurableSingletonClass: post('whose singletons are measurable'),
    IsProbabilityMeasure: n('probability measure'), 'MeasureTheory.IsProbabilityMeasure': n('probability measure'),
    IsFiniteMeasure: n('finite measure'), 'MeasureTheory.IsFiniteMeasure': n('finite measure'),
    SigmaFinite: n('σ-finite measure'), 'MeasureTheory.SigmaFinite': n('σ-finite measure'),
    // sets and logic
    Fintype: adj('finite'), Finite: adj('finite'), Infinite: adj('infinite'), Countable: adj('countable'), Encodable: adj('countable'),
    Nonempty: adj('nonempty'), Inhabited: adj('nonempty'), IsEmpty: adj('empty'), Unique: post('with exactly one element'),
    Subsingleton: post('with at most one element'),
    DecidableEq: DROP, DecidablePred: DROP, DecidableRel: DROP, Decidable: DROP, DecidableLT: DROP, DecidableLE: DROP,
    NeZero: { c: 'hyp', lean: (a) => `${a[0]} ≠ 0` }, Fact: { c: 'hyp', lean: (a) => a[0].replace(/^\((.*)\)$/s, '$1') },
    // category theory
    Category: n('category'), 'CategoryTheory.Category': n('category'),
  };

  const SIMPLE = /^[\p{L}_][\p{L}\p{Nd}_'₀-₉]*$/u;
  const VOWEL_SOUND = /^(?![Uu]ni|[Ee]u|[Oo]ne\b|σ|T[₀-₄])[aeiouAEIOU]/;
  const article = (phrase) => (VOWEL_SOUND.test(phrase) ? 'an ' : 'a ');

  // What an instance `[cls args…]` is: bookkeeping to drop, a hypothesis, a statement
  // about one named subject, or something this book does not cover.
  function classify(cls, args) {
    const entry = Object.hasOwn(PHRASES, cls) ? PHRASES[cls] : null;
    if (!entry) return { kind: 'unknown' };
    if (entry.c === 'drop') return { kind: 'drop' };
    if (entry.c === 'hyp') return args.length === 1 ? { kind: 'hyp', lean: entry.lean(args) } : { kind: 'unknown' };
    const arity = entry.arity || (entry.scalar ? 2 : 1);
    if (args.length !== arity) return { kind: 'unknown' };
    const subject = args[entry.subj ?? args.length - 1];
    return SIMPLE.test(subject) ? { kind: 'about', subject } : { kind: 'unknown' };
  }

  // "{0}" in a phrase stands for an argument, shown as a formula.
  const fill = (text, args) => text.split(/(\{\d\})/).filter(Boolean).map((p) => (/^\{\d\}$/.test(p) ? { lean: args[+p[1]] } : p));
  // A noun over a scalar: "real …" / "complex …" for ℝ and ℂ, "… over K" otherwise.
  const overScalar = (noun, scalar, plain) =>
    !plain && scalar === 'ℝ' ? ['real ' + noun] : !plain && scalar === 'ℂ' ? ['complex ' + noun] : [noun + ' over ', { lean: scalar }];

  // Describes one subject from the instances about it. `classesOf(name)` gives the class
  // names known for any other subject. Returns the complement of "Let X be …" as pieces
  // (strings and { lean }), or null when there is nothing to say.
  function describe(instances, { isType, classesOf }) {
    const left = new Map(instances.map((i) => [i.cls, i]));
    const has = (...names) => names.find((c) => left.has(c));
    const take = (...names) => { const got = names.map((c) => left.get(c)); names.forEach((c) => left.delete(c)); return got; };
    const nouns = [], adjs = [], posts = [];
    let whole = null;

    // Known combinations first: several classes that together name one structure.
    const group = has('NormedAddCommGroup', 'SeminormedAddCommGroup');
    if (group && left.has('InnerProductSpace')) {
      const [, ips] = take(group, 'InnerProductSpace');
      const complete = left.has('CompleteSpace') && take('CompleteSpace');
      nouns.push(overScalar(complete ? 'Hilbert space' : 'inner product space', ips.args[0]));
    } else if (group && left.has('NormedSpace')) {
      const [, ns] = take(group, 'NormedSpace');
      const complete = left.has('CompleteSpace') && take('CompleteSpace');
      nouns.push(overScalar(complete ? 'Banach space' : group === 'NormedAddCommGroup' ? 'normed space' : 'seminormed space', ns.args[0]));
    }
    const additive = has('AddCommGroup', 'AddCommMonoid');
    if (additive && left.has('Module')) {
      const [, mod] = take(additive, 'Module');
      const scalar = mod.args[0];
      const field = /^[ℝℂℚ]$/.test(scalar) || ['Field', 'DivisionRing', 'NormedField', 'NontriviallyNormedField', 'RCLike'].some((c) => classesOf(scalar).has(c));
      nouns.push(field ? overScalar('vector space', scalar) : ['module over ', { lean: scalar }]);
    }
    const metric = has('MetricSpace', 'PseudoMetricSpace');
    if (metric && left.has('NormedAddTorsor')) {
      const [, torsor] = take(metric, 'NormedAddTorsor');
      const euclidean = classesOf(torsor.args[0]).has('InnerProductSpace');
      nouns.push([(euclidean ? 'Euclidean affine space over ' : 'normed affine space over '), { lean: torsor.args[0] }]);
    }
    const ring = has('Field', 'CommRing', 'Ring', 'CommSemiring', 'Semiring');
    if (ring && left.has('LinearOrder') && left.has('IsStrictOrderedRing')) {
      take(ring, 'LinearOrder', 'IsStrictOrderedRing');
      nouns.push(['linearly ordered ' + PHRASES[ring].t]);
    } else if (ring && left.has('IsDomain') && (ring === 'CommRing' || ring === 'Ring')) {
      take(ring, 'IsDomain');
      nouns.push([ring === 'CommRing' ? 'integral domain' : 'domain']);
    } else if (ring && ring !== 'Field' && left.has('Algebra')) {
      const [, alg] = take(ring, 'Algebra');
      nouns.push([(ring.startsWith('Comm') ? 'commutative algebra over ' : 'algebra over '), { lean: alg.args[0] }]);
    }
    if (left.has('LieRing') && left.has('LieAlgebra')) {
      const [, lie] = take('LieRing', 'LieAlgebra');
      nouns.push(['Lie algebra over ', { lean: lie.args[0] }]);
    }
    for (const [structure, topo, name] of [['Group', 'IsTopologicalGroup', 'topological group'], ['Group', 'TopologicalGroup', 'topological group'],
      ['Ring', 'IsTopologicalRing', 'topological ring'], ['Ring', 'TopologicalRing', 'topological ring']]) {
      if (left.has(structure) && left.has('TopologicalSpace') && left.has(topo)) { take(structure, 'TopologicalSpace', topo); nouns.push([name]); }
    }

    // Then one class at a time.
    for (const inst of left.values()) {
      const entry = PHRASES[inst.cls];
      if (entry.c === 'be') whole = entry.t;
      else if (entry.c === 'adj') adjs.push(entry.t);
      else if (entry.c === 'post') posts.push(fill(entry.t, inst.args));
      else nouns.push(entry.scalar ? overScalar(entry.t, inst.args[0], entry.plain) : fill(entry.t, inst.args));
    }

    // "compact Hausdorff space", not "Hausdorff compact space": separation axioms sit next to the noun.
    const near = (a) => (/^(Hausdorff|T[₀-₄]|regular|normal)$/.test(a) ? 1 : 0);
    adjs.sort((a, b) => near(a) - near(b));
    if (whole) return whole;
    if (!nouns.length && isType && (adjs.length || posts.length)) nouns.push(['type']);
    if (!nouns.length && !adjs.length) return null; // only a trailing phrase and nothing to attach it to
    const out = [];
    if (nouns.length) {
      nouns.forEach((noun, k) => {
        const lead = k === 0 && adjs.length ? adjs.join(' ') + ' ' : '';
        out.push((k ? ' and ' : '') + article(lead + noun[0]) + lead, ...noun);
      });
      posts.forEach((p) => out.push(' ', ...p));
    } else out.push(adjs.join(' and '));
    // Merge neighbouring strings so the result reads as running text.
    return out.reduce((acc, p) => {
      if (typeof p === 'string' && typeof acc[acc.length - 1] === 'string') acc[acc.length - 1] += p;
      else acc.push(p);
      return acc;
    }, []);
  }

  // The operation behind a notation: what its node shows instead of a bare name.
  const NOTATION = {
    'Norm.norm': ['\\| x \\|', 'norm'], 'NNNorm.nnnorm': ['\\| x \\|_{+}', 'norm, as a non-negative real'],
    'ENorm.enorm': ['\\| x \\|_{e}', 'extended norm'],
    'Dist.dist': ['d(x, y)', 'distance'], 'NNDist.nndist': ['d(x, y)', 'distance, as a non-negative real'],
    'EDist.edist': ['d(x, y)', 'extended distance'],
    'Inner.inner': ['\\langle x, y \\rangle', 'inner product'],
    'VSub.vsub': ['p - q', 'the vector from q to p'], 'VAdd.vadd': ['v + p', 'a vector added to a point'],
    'HAdd.hAdd': ['a + b', 'addition'], 'Add.add': ['a + b', 'addition'], 'HSub.hSub': ['a - b', 'subtraction'], 'Sub.sub': ['a - b', 'subtraction'],
    'HMul.hMul': ['a \\cdot b', 'multiplication'], 'Mul.mul': ['a \\cdot b', 'multiplication'],
    'HDiv.hDiv': ['a / b', 'division'], 'Div.div': ['a / b', 'division'], 'HPow.hPow': ['a^{b}', 'power'], 'Pow.pow': ['a^{b}', 'power'],
    'HSMul.hSMul': ['c \\bullet x', 'scalar multiplication'], 'SMul.smul': ['c \\bullet x', 'scalar multiplication'],
    'Neg.neg': ['-a', 'negation'], 'Inv.inv': ['a^{-1}', 'inverse'], 'Zero.zero': ['0', 'zero'], 'One.one': ['1', 'one'],
    'LE.le': ['a \\le b', 'order'], 'LT.lt': ['a < b', 'strict order'], 'Membership.mem': ['a \\in s', 'membership'],
    'HasSubset.Subset': ['s \\subseteq t', 'inclusion'], 'Union.union': ['s \\cup t', 'union'], 'Inter.inter': ['s \\cap t', 'intersection'],
    'SDiff.sdiff': ['s \\setminus t', 'difference'], 'Compl.compl': ['s^{c}', 'complement'],
    'Max.max': ['a \\sqcup b', 'supremum of two'], 'Min.min': ['a \\sqcap b', 'infimum of two'],
    'Top.top': ['\\top', 'greatest element'], 'Bot.bot': ['\\bot', 'least element'],
    'Dvd.dvd': ['a \\mid b', 'divisibility'], 'Star.star': ['x^{\\star}', 'star'],
    'DFunLike.coe': ['f(x)', 'applying a function-like object'], 'SetLike.coe': ['S', 'a structure seen as a set'],
    'SProd.sprod': ['s \\times t', 'product of sets'], 'HasQuotient.Quotient': ['A / B', 'quotient'],
    'Quiver.Hom': ['X \\longrightarrow Y', 'morphisms from X to Y'],
    'CategoryTheory.CategoryStruct.comp': ['f \\gg g', 'composition, f then g'], 'CategoryTheory.CategoryStruct.id': ['\\mathbb{1}_{X}', 'identity morphism'],
  };

  const nounOf = (cls) => (Object.hasOwn(PHRASES, cls) && PHRASES[cls].c === 'n' && !PHRASES[cls].t.includes('{') ? PHRASES[cls].t : null);
  const last = (name) => name.slice(name.lastIndexOf('.') + 1);

  // What to say about a declaration Lean generated and the source never states: a notation's
  // operation ({ tex, words }), a structure passing to one it extends ("every ring is a
  // semiring"; `parent` names that structure), or a field of a structure. `words` may mark
  // Lean names with backticks. Null when the name gives nothing to go on.
  function projection(name, parent) {
    if (Object.hasOwn(NOTATION, name)) return { tex: NOTATION[name][0], words: NOTATION[name][1] };
    const dot = name.lastIndexOf('.');
    if (dot < 0) return null;
    const owner = last(name.slice(0, dot));
    if (parent) {
      const from = nounOf(owner), to = nounOf(last(parent));
      return { words: from && to ? `every ${from} is ${article(to)}${to}` : `every \`${owner}\` is ${article(last(parent))}\`${last(parent)}\`` };
    }
    return { words: `\`${last(name)}\` of ${article(owner)}\`${owner}\`` };
  }

  // Predicates: how a property is said. `{k}` is the k-th argument, shown as a formula;
  // ⟦…⟧ is a piece of formula written out; the rest is prose. Each entry gives the wording,
  // how many arguments the predicate takes, and how many optional ones may follow (a measure,
  // usually). `dot: true` marks those also written after their subject: `s.Nonempty`.
  const P = (text, arity, extra = 0, dot = false) => ({ text, arity, extra, dot });
  const PREDICATES = {
    // functions
    Continuous: P('{0} is continuous', 1), ContinuousOn: P('{0} is continuous on {1}', 2), ContinuousAt: P('{0} is continuous at {1}', 2),
    ContinuousWithinAt: P('{0} is continuous at {2} within {1}', 3), UniformContinuous: P('{0} is uniformly continuous', 1),
    UniformContinuousOn: P('{0} is uniformly continuous on {1}', 2), LipschitzWith: P('{1} is Lipschitz with constant {0}', 2),
    Differentiable: P('{1} is differentiable', 2), DifferentiableOn: P('{1} is differentiable on {2}', 3),
    DifferentiableAt: P('{1} is differentiable at {2}', 3), DifferentiableWithinAt: P('{1} is differentiable at {3} within {2}', 4),
    HasDerivAt: P('{0} has derivative {1} at {2}', 3), HasDerivWithinAt: P('{0} has derivative {1} at {3} within {2}', 4),
    HasStrictDerivAt: P('{0} has strict derivative {1} at {2}', 3),
    HasFDerivAt: P('{0} has Fréchet derivative {1} at {2}', 3), HasFDerivWithinAt: P('{0} has Fréchet derivative {1} at {3} within {2}', 4),
    HasStrictFDerivAt: P('{0} has strict Fréchet derivative {1} at {2}', 3),
    ContDiff: P('{2} is of class ⟦C^{{1}}⟧', 3), ContDiffOn: P('{2} is of class ⟦C^{{1}}⟧ on {3}', 4),
    ContDiffAt: P('{2} is of class ⟦C^{{1}}⟧ at {3}', 4), ContDiffWithinAt: P('{2} is of class ⟦C^{{1}}⟧ at {4} within {3}', 5),
    AnalyticAt: P('{1} is analytic at {2}', 3), AnalyticOn: P('{1} is analytic on {2}', 3),
    Injective: P('{0} is injective', 1, 0, true), Surjective: P('{0} is surjective', 1, 0, true), Bijective: P('{0} is bijective', 1, 0, true),
    InjOn: P('{0} is injective on {1}', 2), SurjOn: P('{0} maps {1} onto {2}', 3), BijOn: P('{0} is a bijection from {1} to {2}', 3),
    MapsTo: P('{0} maps {1} into {2}', 3), EqOn: P('⟦{0} = {1}⟧ on {2}', 3), Involutive: P('{0} is an involution', 1),
    LeftInverse: P('{0} is a left inverse of {1}', 2), RightInverse: P('{0} is a right inverse of {1}', 2), Periodic: P('{0} is periodic with period {1}', 2),
    Monotone: P('{0} is monotone', 1), Antitone: P('{0} is antitone', 1), StrictMono: P('{0} is strictly increasing', 1), StrictAnti: P('{0} is strictly decreasing', 1),
    MonotoneOn: P('{0} is monotone on {1}', 2), AntitoneOn: P('{0} is antitone on {1}', 2),
    StrictMonoOn: P('{0} is strictly increasing on {1}', 2), StrictAntiOn: P('{0} is strictly decreasing on {1}', 2),
    ConvexOn: P('{2} is convex on {1}', 3), ConcaveOn: P('{2} is concave on {1}', 3),
    StrictConvexOn: P('{2} is strictly convex on {1}', 3), StrictConcaveOn: P('{2} is strictly concave on {1}', 3),
    // measure and summation
    Measurable: P('{0} is measurable', 1), AEMeasurable: P('{0} is a.e. measurable', 1, 1), StronglyMeasurable: P('{0} is strongly measurable', 1),
    AEStronglyMeasurable: P('{0} is a.e. strongly measurable', 1, 1), Integrable: P('{0} is integrable', 1, 1), IntegrableOn: P('{0} is integrable on {1}', 2, 1),
    IntervalIntegrable: P('{0} is integrable on ⟦[{2}, {3}]⟧', 4), MemLp: P('{0} is in ⟦L^{{1}}⟧', 2, 1),
    MeasurableSet: P('{0} is measurable', 1), NullMeasurableSet: P('{0} is null-measurable', 1, 1),
    Summable: P('{0} is summable', 1), Multipliable: P('{0} is multipliable', 1), HasSum: P('{0} has sum {1}', 2), HasProd: P('{0} has product {1}', 2),
    // sets
    IsOpen: P('{0} is open', 1), IsClosed: P('{0} is closed', 1), IsCompact: P('{0} is compact', 1), IsConnected: P('{0} is connected', 1),
    IsPreconnected: P('{0} is preconnected', 1), Dense: P('{0} is dense', 1), IsBounded: P('{0} is bounded', 1), IsClopen: P('{0} is clopen', 1),
    Convex: P('{1} is convex', 2), BddAbove: P('{0} is bounded above', 1), BddBelow: P('{0} is bounded below', 1),
    Nonempty: P('{0} is nonempty', 1, 0, true), Finite: P('{0} is finite', 1, 0, true), Infinite: P('{0} is infinite', 1, 0, true),
    Countable: P('{0} is countable', 1, 0, true), Subsingleton: P('{0} has at most one element', 1, 0, true),
    IsLeast: P('{1} is the least element of {0}', 2), IsGreatest: P('{1} is the greatest element of {0}', 2),
    IsLUB: P('{1} is the least upper bound of {0}', 2), IsGLB: P('{1} is the greatest lower bound of {0}', 2),
    Disjoint: P('{0} and {1} are disjoint', 2), LinearIndependent: P('{1} is linearly independent over {0}', 2),
    // elements
    Prime: P('{0} is prime', 1, 0, true), Irreducible: P('{0} is irreducible', 1), IsUnit: P('{0} is a unit', 1), IsNilpotent: P('{0} is nilpotent', 1),
    Even: P('{0} is even', 1), Odd: P('{0} is odd', 1), IsSquare: P('{0} is a square', 1), Squarefree: P('{0} is squarefree', 1),
    Irrational: P('{0} is irrational', 1), IsIntegral: P('{1} is integral over {0}', 2), IsAlgebraic: P('{1} is algebraic over {0}', 2),
    Transcendental: P('{1} is transcendental over {0}', 2), IsCoprime: P('{0} and {1} are coprime', 2), Coprime: P('{0} and {1} are coprime', 2, 0, true),
    Commute: P('{0} and {1} commute', 2), IsMin: P('{0} is minimal', 1), IsMax: P('{0} is maximal', 1),
    IsBot: P('{0} is the least element', 1), IsTop: P('{0} is the greatest element', 1),
  };
  // Namespaces in which these names keep their usual meaning (`Function.Injective`, `Set.Finite`).
  const PREDICATE_NS = new Set(['Function', 'Set', 'Nat', 'Int', 'MeasureTheory', 'Bornology', 'Filter']);

  // The wording of a predicate, or null. `dotted` asks for one that may follow its subject.
  function predicate(name, dotted) {
    const dot = name.lastIndexOf('.');
    if (dot >= 0 && !PREDICATE_NS.has(name.slice(0, dot))) return null;
    const entry = PREDICATES[name.slice(dot + 1)];
    return Object.hasOwn(PREDICATES, name.slice(dot + 1)) && (!dotted || entry.dot) ? entry : null;
  }

  return { classify, describe, projection, predicate };
});
