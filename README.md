# Mathlib graph navigator

Look up one Mathlib declaration and walk its dependencies in both directions:
what it depends on, and what depends on it.

Data: [CloK-Lab/MathlibGraph](https://huggingface.co/datasets/CloK-Lab/MathlibGraph)
(Mathlib commit `534cf0b`, 2 Feb 2026 — 308,129 declarations, 8.4 million edges).

## Requirements

Node.js 22 or newer and `git` (the build clones Mathlib's source). No npm packages.

## Run

```sh
node build.js     # once: downloads ~640 MB of data, clones Mathlib (~150 MB), builds data/mathlib.db (~340 MB)
node server.js    # then open http://127.0.0.1:5173/
```

`PORT=8080 node server.js` uses another port. Node prints an "ExperimentalWarning"
about SQLite; add `--disable-warning=ExperimentalWarning` to hide it.

## Optional: statements from Lean itself

The source text leaves out what Lean infers. `theorem continuousOn_cos {s} :
ContinuousOn cos s` does not say that `s` is a set of real numbers; Lean works that
out. With Lean set up, the server asks it for each declaration's full statement the
first time that declaration is on screen, and remembers the answer.

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
cd data/mathlib4 && ~/.elan/bin/lake exe cache get    # precompiled Mathlib, no compiling
```

That takes about 10.6 GB on disk (3.3 GB of Lean toolchain in `~/.elan`, 7.3 GB of
compiled Mathlib in `data/mathlib4/.lake`) and a few minutes to download. After it,
`node server.js` starts Lean in the background: loading Mathlib takes about 25
seconds, during which the page works from the source text; a view of new nodes then
gets its statements in a fraction of a second. The top bar shows "Lean: ready".

- The Lean program is `lean/Signatures.lean`; `lib/lean.js` runs it and keeps its
  answers in `data/lean-cache.v3.db`, which survives `node build.js`.
- It covers declarations the source never writes out (the ones Lean generates), and
  switches on Mathlib's common scoped notations so that statements print as their
  authors wrote them.
- With Lean, the column next to the focus is split in two: what the statement itself
  involves (drawn with green edges), and what only the proof uses. On the right, the
  results that state something about the focus come apart from those that merely use
  it in their proof. Lean reports this exactly, from the compiled declarations.
- With Lean, a theorem can carry a tag saying what kind of statement it is, from three
  tests that use no naming convention and so apply to any Lean project. **cast rule**:
  with the canonical maps erased, both sides say the same thing (`ι(r/s) = ι(r)/ι(s)`).
  **by definition**: Lean proves it by unfolding definitions. **corollary**: its proof
  rests on a single other result, one that is specific and has an argument of its own.
  **restates**: it says the same as the one result it rests on. **hide bookkeeping**
  hides the first two kinds.
- Without Lean, nothing else changes: statements come from the source text.

## Using it

- Search by name (`/` focuses the search box), or open a link such as
  `http://127.0.0.1:5173/#n=Real.sqrt_nonneg`.
- Each node is a box with the declaration's name on its top edge and, inside, the
  conclusion of its statement typeset as a formula. A definition shows its signature,
  what it takes and what it gives ("arg : ℂ → ℝ"), not how it is computed; without
  a stated type it shows the opening of its docstring; a declaration with neither shows its name only.
  An abbreviation shows what it stands for ("Name := expression"). Declarations
  Lean generates are worded from their name: a notation's operation shows its sign
  (`Norm.norm` as ‖x‖), `Semiring.toNonAssocSemiring` reads "every semiring is a
  non-associative semiring", and a structure's field reads "`obj` of a `Functor`". Hover a
  node, or a dependency's name in the proof, for a card with its docstring and
  full statement, hypotheses included. **nodes as** switches to
  compact name-only boxes.
- Dependencies are on the left, dependents on the right. Arrows point from a
  declaration to what it depends on. Click a node to focus on it; the browser's
  back and forward buttons walk through what you visited.
- Each node shows, at its right edge, how many declarations in Mathlib rest on it,
  directly or through other results, with a bar under the name on a log scale. That
  makes it visible when a theorem nobody cites (0) rests on a lemma that hundreds of
  others need. The count is for the whole graph, whatever the filters. It is
  computed by `build.js` (the dataset only has direct counts): exact up to 128,
  an estimate within a few percent above that. The tooltip and the side panel give
  the direct count as well.
- **nodes show** picks what that number and bar measure: all uses (the default),
  direct uses only, or PageRank. PageRank is shown as a multiple of the average
  declaration's score ("0.2×", "620×"), since the raw values are tiny fractions.
  The choice is remembered in the browser.
- **explicit only** hides the dependencies Lean filled in by itself (typeclass
  instances and similar — about 74% of all edges). Dashed edges are those.
- **hide Lean plumbing** (on by default) leaves out the logic and notation machinery
  of Lean's core library, such as `Eq.mpr`, `propext`, `HAdd.hAdd` and `OfNat.ofNat`,
  which nearly every proof touches. Core declarations about data (`Nat`, `Int`,
  `List` …) stay. It also leaves out Mathlib's inheritance projections (`X.toY`
  where the structure X extends Y). Everything else from Mathlib stays. The column header says how many
  neighbours the filters hid.
- **theorems only** keeps just the theorems and lemmas around the focus and hides
  definitions, structures, instances and the rest. The focus itself is always shown.
- **depth** shows 1–3 steps away. Each level shows the top 10/25/50/100
  declarations by PageRank; the column header says how many there are in total.
- The side panel shows the focused declaration's Lean statement; a
  panel below the graph shows its proof (or, for a definition, its body). The code
  is syntax-coloured, and each name that is one of the declaration's dependencies
  is underlined: click it to focus on that dependency, or hover it to pick out its
  node in the graph. Dependencies named in the code are always drawn, listed first,
  in addition to the top-ranked ones.
  The proof is shown as an outline by default: the claims its author states along the
  way (`have`, `obtain`, `suffices`, `calc` …), typeset, with the comments as prose and
  a count of the tactic lines in between; "Lean" switches to the source. The outline
  is read from the text (`public/lean-outline.js`), not from Lean's goals.
  Statements are read from the clone of Mathlib's `master` branch that `build.js`
  makes in `data/mathlib4` (delete that folder and build again to refresh it), so
  no internet access is needed while browsing; the "Source file" link opens that
  line on GitHub. Master is newer than the snapshot: moved files are followed
  through their deprecation shims, and declarations Lean generates automatically
  have no statement to show (about a quarter of them).
- A band above the graph shows the declaration's docstring and its statement typeset as mathematics, with a
  "Copy LaTeX" button. This is a rule-based conversion that stays close to Lean's
  wording (hypotheses listed, then the conclusion); it is typeset with KaTeX,
  loaded from a CDN. Typeclass assumptions are put into words from a phrasebook
  (`public/lean-phrases.js`): `[Field K]` reads "K is a field". To teach it a new
  class, add one line to `PHRASES` there; classes it does not know keep their
  Lean name.
- **notation** switches the typeset statement between International and
  French / Belgian conventions: the angle ABC under a hat instead of ∠ABC, open
  intervals as ]a, b[ instead of (a, b), and slanted ≤ ≥. The wording stays in
  English. The choice is remembered in the browser.
- Standard constants and functions are written with their usual sign instead of
  their Lean name: π, i, exp, log, sin, cos, arcsin, √, |x|, n!, binomials, gcd,
  max, Re and Im. This applies only where the name has its standard meaning
  (`Real.pi`, `Complex.exp`, `Nat.gcd`); `Finset.pi` keeps its Lean name. The table
  is at the top of `ident` in `public/lean-latex.js`.
- Standard spaces are written with their symbol: `Real.Angle` is ℝ/2πℤ, `ZMod n` is
  ℤ/nℤ, `NNReal` is ℝ≥0, `ENNReal` is [0, ∞], `Circle` is 𝕊¹, `Matrix m n R` is
  M_{m×n}(R), `Rˣ` the units of R. The tables `SPACES` and `SPACES_OF` are next to
  `ident` in `public/lean-latex.js`.
- A coercion (Lean's `↑x`: a real number regarded as a complex one, a natural number
  as a real) is written as a named map: "Let ι : ℝ → ℂ be the canonical map. Then
  ι(r/s) = ι(r)/ι(s)". It is never left out: without it, a statement about the map
  reads `r/s = r/s`. With several maps in one statement they are told apart by
  where they land, ι_ℝ and ι_ℂ.
- Predicates are put into words: `ContinuousOn f s` reads "f is continuous on s",
  `StrictConcaveOn ℝ s f` "f is strictly concave on s", `s.Nonempty` "s is nonempty",
  and `Tendsto f atTop (𝓝 a)` "f → a at +∞". About 110 are covered, in `PREDICATES`
  in `public/lean-phrases.js`; a predicate not listed there keeps its Lean name.
- Drag or scroll to move; pinch or ⌘/Ctrl-scroll to zoom.

## A rule for the typeset statement

The LaTeX rendering changes **notation, never the statement**. Powers, fractions,
intervals, "x ∈ K", chained inequalities and the typeclass phrasebook are all
different ways of writing exactly what Lean says. Replacing a statement by an
equivalent one is not allowed, even when a textbook would prefer it: Mathlib's
"the angle between x and y is π/2" is not rewritten as "x ⊥ y". That rewrite was
tried on 2026-11-26 and removed the same day, because the page would then show a
claim that is not the one Mathlib proves under that name.

## Known limitations

Two approximations in the typeset (LaTeX) statement are deliberate shortcuts, not bugs:

- **`Module.Finite` is worded "finitely generated".** Over a field a reader would
  say "finite-dimensional". The phrasebook (`PHRASES['Module.Finite']` in
  `public/lean-phrases.js`) does not check whether the scalars form a field for
  this class, although it does for `Module` ("vector space").
- **Telling hypotheses from variables is a naming guess.** A binder goes under
  "Assume …" instead of "Let …" when its type contains a relation symbol, or its
  name starts with `h`, or its name contains an underscore (such as `f_mble`).
  This is the `named` test in `toLatex` in `public/lean-latex.js`; it will
  occasionally misclassify a real variable whose name has an underscore.

## Tests

```sh
node --disable-warning=ExperimentalWarning --test
```

## Layout

| File | What it does |
|---|---|
| `build.js` | Downloads the CSVs and builds the database |
| `lib/csv.js` | CSV reader |
| `lib/graphdb.js` | Database build, name search, neighbourhood query |
| `lib/reach.js` | Counts each declaration's direct and indirect dependents |
| `lib/lean.js` | Runs Lean, asks it for statements, remembers the answers |
| `lean/Signatures.lean` | The Lean program that prints a declaration's full statement |
| `server.js` | `/api/search`, `/api/node`, and the page |
| `public/index.html` | The whole interface |
| `public/lean.js` | Lean syntax colouring and dependency links |
| `public/lean-latex.js` | Lean statement to LaTeX |
| `public/lean-phrases.js` | Typeclass phrasebook |
| `lib/leansource.js` | Finds a declaration's statement, proof and context in a Lean file |
