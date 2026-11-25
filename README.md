# Mathlib graph navigator

Look up one Mathlib declaration and walk its dependencies in both directions:
what it depends on, and what depends on it.

Data: [CloK-Lab/MathlibGraph](https://huggingface.co/datasets/CloK-Lab/MathlibGraph)
(Mathlib commit `534cf0b`, 2 Feb 2026 — 308,129 declarations, 8.4 million edges).

## Requirements

Node.js 22 or newer. No npm packages.

## Run

```sh
node build.js     # once: downloads ~640 MB into data/ and builds data/mathlib.db (~260 MB)
node server.js    # then open http://127.0.0.1:5173/
```

`PORT=8080 node server.js` uses another port. Node prints an "ExperimentalWarning"
about SQLite; add `--disable-warning=ExperimentalWarning` to hide it.

## Using it

- Search by name (`/` focuses the search box), or open a link such as
  `http://127.0.0.1:5173/#n=Real.sqrt_nonneg`.
- Dependencies are on the left, dependents on the right. Arrows point from a
  declaration to what it depends on. Click a node to focus on it; the browser's
  back and forward buttons walk through what you visited.
- **explicit only** hides the dependencies Lean filled in by itself (typeclass
  instances and similar — about 74% of all edges). Dashed edges are those.
- **depth** shows 1–3 steps away. Each level shows the top 25/50/100
  declarations by PageRank; the column header says how many there are in total.
- The side panel shows the focused declaration's Lean statement and docstring; a
  panel below the graph shows its proof (or, for a definition, its body). The code
  is syntax-coloured, and each name that is one of the declaration's dependencies
  is underlined: click it to focus on that dependency, or hover it to pick out its
  node in the graph. Dependencies named in the code are always drawn, listed first,
  in addition to the top-ranked ones.
  The server reads them from the source file on Mathlib's `master` branch on
  GitHub (so this part needs internet access), and the "Source file" link opens
  that line. Master is newer than the snapshot: moved files are followed through
  their deprecation shims, and declarations Lean generates automatically have
  no statement to show.
- Above the Lean statement, the side panel shows it typeset as mathematics, with a
  "Copy LaTeX" button. This is a rule-based conversion that stays close to Lean's
  wording (hypotheses listed, then the conclusion); it is typeset with KaTeX,
  loaded from a CDN. Typeclass assumptions are put into words from a phrasebook
  (`public/lean-phrases.js`): `[Field K]` reads "K is a field". To teach it a new
  class, add one line to `PHRASES` there; classes it does not know keep their
  Lean name.
- Drag or scroll to move; pinch or ⌘/Ctrl-scroll to zoom.

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
| `server.js` | `/api/search`, `/api/node`, and the page |
| `public/index.html` | The whole interface |
| `public/lean.js` | Lean syntax colouring and dependency links |
| `public/lean-latex.js` | Lean statement to LaTeX |
| `public/lean-phrases.js` | Typeclass phrasebook |
| `lib/leansource.js` | Finds a declaration's statement, proof and context in a Lean file |
