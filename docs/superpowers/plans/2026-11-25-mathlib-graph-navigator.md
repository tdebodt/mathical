# Mathlib Graph Navigator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A local web app to look up one Mathlib declaration and walk its dependencies in and out.

**Architecture:** `build.js` downloads two CSVs from Hugging Face and loads them into a SQLite file. `server.js` answers search and neighbourhood queries from that file and serves one static page. `index.html` draws a layered SVG graph around the focused declaration.

**Tech Stack:** Node.js 22+ with built-ins only (`node:sqlite`, `node:http`, `node:test`, `fetch`). Plain HTML/CSS/JS, hand-drawn SVG.

**Spec:** `docs/superpowers/specs/2026-11-25-mathlib-graph-navigator-design.md`

## Global Constraints

- No npm dependencies; no `package.json` scripts beyond `"type": "commonjs"` being the default (no package.json needed).
- Node 22+; suppress the `node:sqlite` ExperimentalWarning only by documenting `--disable-warning=ExperimentalWarning` in the README commands.
- Data source base URL: `https://huggingface.co/datasets/CloK-Lab/MathlibGraph/resolve/main/`; files `mathlib_edges.csv` (584 MB) and `v2/declaration/metrics.csv` (57 MB).
- Downloads and the database live in `data/` (git-ignored); downloads are skipped if the file already exists with the expected size.
- Explicit-only is the default everywhere (`explicit=1`).
- The folder is not a git repository; tasks do not commit.
- Tests run with `node --test tests/`.

## Review Focus

1. A hub node (`Eq.refl`, 69,579 dependents): response stays capped and fast; totals still reported. → Task 2 test `caps a large side and reports the total`.
2. Edge endpoints missing from `metrics.csv` (9,526 `@[to_additive]` mirrors were deduplicated out of it): they become stub nodes rather than dropped edges or a crash. → Task 1 test `creates stub nodes for names missing from metrics`.
3. Names with odd characters (`«term_∘_»`, quotes, `%`, `_`) in search and in URLs: treated literally, never as SQL `LIKE` wildcards. → Task 2 test `search treats % and _ literally`; Task 3 test `round-trips a URL-encoded unicode name`.
4. Unknown name or empty query: 404 / empty list, not a 500. → Task 3 tests.
5. Cycles (5,732 nodes are in cycles) at depth 2–3: each node appears once, at its shortest distance, and the focus never reappears as its own neighbour. → Task 2 test `handles cycles`.

---

## File Structure

| File | Responsibility |
|---|---|
| `lib/csv.js` | Streaming CSV line parser (quoted fields supported) |
| `lib/graphdb.js` | Build the database; `search`; `neighborhood` |
| `build.js` | CLI: download files, call `buildDb`, print progress |
| `server.js` | HTTP API + static page |
| `public/index.html` | The whole UI |
| `tests/fixtures/*.csv` | Tiny graph used by all tests |
| `tests/*.test.js` | `node:test` suites |
| `README.md`, `.gitignore` | Run instructions; ignore `data/` |

### Fixture graph (`tests/fixtures/edges.csv`, `metrics.csv`)

`metrics.csv` uses the real 20-column header. Nodes (pagerank descending in this order): `Hub`, `A`, `B`, `C`, `D`, `Thm`, `a%b`, `a_b`, `axb`, `«term_∘_»`, plus `L1`…`L30` (pagerank decreasing with the number).

Edges (`source,target,is_explicit,is_simplifier`; source depends on target):

- `Thm→A` explicit, `Thm→B` explicit, `Thm→Hub` synthesized
- `A→C` explicit, `B→C` explicit, `C→D` explicit
- `D→A` explicit (cycle A→C→D→A)
- `C→C` explicit (self-loop, must be dropped)
- `L1…L30 → Hub` explicit
- `Thm→Ghost` explicit (`Ghost` absent from metrics)

---

### Task 1: CSV parser and database build

**Files:**
- Create: `lib/csv.js`, `lib/graphdb.js`, `tests/fixtures/edges.csv`, `tests/fixtures/metrics.csv`, `tests/build.test.js`, `.gitignore` (`data/`)

**Interfaces:**
- Produces:
  - `csv.parseLine(line: string): string[]` — RFC 4180 fields, handles `"a,b"` and `""` escapes.
  - `csv.rows(path: string): AsyncIterable<Record<string,string>>` — header-keyed rows, streamed with `readline`.
  - `graphdb.buildDb({edgesCsv, metricsCsv, dbPath, onProgress?}): Promise<{nodes:number, edges:number, stubs:number}>`
  - `graphdb.open(dbPath: string): DatabaseSync` (read-only)
  - Schema:
    ```sql
    CREATE TABLE nodes(
      id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, kind TEXT, module TEXT,
      file_module TEXT, in_degree INT, out_degree INT, pagerank REAL DEFAULT 0,
      dag_layer INT, is_tactic_proof INT, tactic_count INT, top_tactic TEXT,
      is_instance INT, instance_class TEXT, to_additive_pair TEXT);
    CREATE TABLE edges(src INT NOT NULL, dst INT NOT NULL, explicit INT NOT NULL,
      PRIMARY KEY(src,dst)) WITHOUT ROWID;
    CREATE INDEX edges_dst ON edges(dst, src);
    ```
    `src` depends on `dst`. Empty CSV cells become NULL; `True`/`False` become 1/0.

- [ ] **Step 1: Write fixtures and failing tests** in `tests/build.test.js` (build into `os.tmpdir()`):

```js
test('parseLine handles quoted commas and escaped quotes', () => {
  assert.deepEqual(parseLine('a,"b,c","d""e",'), ['a', 'b,c', 'd"e', '']);
});
test('loads nodes and edges', () => {
  assert.equal(res.nodes, 41);            // 40 in metrics + Ghost
  assert.equal(res.edges, 38);            // 39 rows minus the C→C self-loop
});
test('creates stub nodes for names missing from metrics', () => {
  const g = db.prepare('SELECT kind, pagerank FROM nodes WHERE name=?').get('Ghost');
  assert.equal(g.kind, null); assert.equal(g.pagerank, 0); assert.equal(res.stubs, 1);
});
test('stores explicit flag and booleans as integers', () => {
  // Thm→Hub explicit = 0, Thm→A explicit = 1
});
test('rebuilding replaces an existing database', ...);
```

- [ ] **Step 2:** Run `node --test tests/build.test.js` — expect failures (module not found).
- [ ] **Step 3:** Implement `lib/csv.js`.
- [ ] **Step 4:** Implement `buildDb`: write to `dbPath + '.tmp'` then rename; `PRAGMA journal_mode=OFF; synchronous=OFF`; one transaction per 200,000 rows; keep a `Map<string, number>` of name→id in memory; insert edges with `INSERT OR IGNORE`; create `edges_dst` after loading; call `onProgress({phase, rows})` every 200,000 rows.
- [ ] **Step 5:** Run the tests — expect all pass.

### Task 2: Queries

**Files:**
- Modify: `lib/graphdb.js`
- Test: `tests/query.test.js`

**Interfaces:**
- Consumes: `open`, schema from Task 1.
- Produces:
  - `search(db, q: string, limit = 20): Node[]` — case-insensitive substring match on `name`; order: exact match, then prefix matches, then the rest, each group by `pagerank DESC`. Empty/whitespace `q` → `[]`. Use `instr(lower(name), lower(?))`, not `LIKE`.
  - `neighborhood(db, name: string, {depth = 1, explicit = true, limit = 25} = {}): Result | null`
    ```ts
    type Node = {id, name, kind, module, file_module, in_degree, out_degree,
                 pagerank, dag_layer, is_tactic_proof, tactic_count, top_tactic,
                 is_instance, instance_class, to_additive_pair};
    type Side = {nodes: (Node & {dist: 1|2|3})[],
                 edges: [srcId: number, dstId: number, explicit: 0|1][],
                 totals: number[]};   // totals[d-1] = nodes found at distance d before the cap
    type Result = {focus: Node, out: Side, in: Side};
    ```
    `out` follows `src→dst` (what the focus depends on); `in` follows the reverse. Breadth-first per side: at each level collect the distinct unseen neighbours of the nodes kept at the previous level, record the count in `totals`, keep the top `limit` by `pagerank DESC, name ASC`, and expand only those. `edges` holds every stored edge whose two endpoints are both in `{focus} ∪ side.nodes`, in true `src,dst` orientation. `depth` is clamped to 1–3, `limit` to 1–200. Unknown name → `null`.

- [ ] **Step 1: Write failing tests**

```js
test('direct explicit dependencies', () => {
  const r = neighborhood(db, 'Thm');
  assert.deepEqual(names(r.out), ['A', 'B', 'Ghost']);   // pagerank order, stub last
  assert.deepEqual(r.out.totals, [3]);
  assert.deepEqual(names(r.in), []);
});
test('explicit=false adds synthesized edges', () => {
  assert.ok(names(neighborhood(db, 'Thm', {explicit: false}).out).includes('Hub'));
});
test('dependents come back on the in side', () => {
  assert.deepEqual(names(neighborhood(db, 'C').in), ['A', 'B']);
});
test('caps a large side and reports the total', () => {
  const r = neighborhood(db, 'Hub', {limit: 10});
  assert.equal(r.in.nodes.length, 10); assert.deepEqual(r.in.totals, [30]);
  assert.equal(r.in.nodes[0].name, 'L1');
});
test('handles cycles', () => {
  const r = neighborhood(db, 'A', {depth: 3});
  assert.deepEqual(r.out.nodes.map(n => [n.name, n.dist]), [['C', 1], ['D', 2]]);
  assert.ok(r.out.edges.some(([s, d]) => s === id('D') && d === id('A')));
});
test('unknown name returns null', () => assert.equal(neighborhood(db, 'Nope'), null));
test('search ranks exact, then prefix, then substring', () => {
  assert.deepEqual(search(db, 'a').slice(0, 1).map(n => n.name), ['A']);
});
test('search treats % and _ literally', () => {
  assert.deepEqual(search(db, 'a%b').map(n => n.name), ['a%b']);
  assert.deepEqual(search(db, 'a_b').map(n => n.name), ['a_b']);
});
test('search finds unicode names and returns [] for blank', () => {
  assert.equal(search(db, '∘')[0].name, '«term_∘_»');
  assert.deepEqual(search(db, '  '), []);
});
```

- [ ] **Step 2:** Run `node --test tests/query.test.js` — expect failures.
- [ ] **Step 3:** Implement `search` and `neighborhood`.
- [ ] **Step 4:** Run `node --test tests/` — expect all pass.

### Task 3: HTTP server

**Files:**
- Create: `server.js`, `public/index.html` (placeholder `<title>Mathlib graph navigator</title>`), `tests/server.test.js`

**Interfaces:**
- Consumes: `open`, `search`, `neighborhood`.
- Produces:
  - `createServer(dbPath: string): http.Server` (exported; `server.js` listens only when run directly, on `PORT` or 5173, host `127.0.0.1`).
  - `GET /api/search?q=&limit=` → `200 Node[]`
  - `GET /api/node?name=&depth=&explicit=0|1&limit=` → `200 Result`; missing `name` → `400 {"error":"name is required"}`; unknown → `404 {"error":"not found"}`
  - `GET /` → `public/index.html`; anything else → 404. JSON responses are `application/json; charset=utf-8`.
  - If the database file is missing at startup: print `Run "node build.js" first.` and exit 1.

- [ ] **Step 1: Write failing tests** (server on port 0 against the fixture database, using `fetch`):

```js
test('search endpoint', ...);                       // q=Th → [Thm]
test('node endpoint defaults to explicit depth 1', ...);
test('explicit=0 and depth=2 are honoured', ...);
test('round-trips a URL-encoded unicode name', ...); // name=%C2%ABterm_%E2%88%98_%C2%BB → 200
test('missing name is 400, unknown name is 404', ...);
test('non-numeric depth and limit fall back to defaults', ...);
test('serves the page at / and 404s elsewhere, including /../server.js', ...);
```

- [ ] **Step 2:** Run — expect failures.
- [ ] **Step 3:** Implement `server.js`.
- [ ] **Step 4:** Run `node --test tests/` — expect all pass.

### Task 4: Build CLI and real data

**Files:**
- Create: `build.js`, `README.md`

**Interfaces:**
- Consumes: `buildDb`.
- Produces: `node build.js` → `data/mathlib_edges.csv`, `data/metrics.csv`, `data/mathlib.db`.

- [ ] **Step 1:** Implement `build.js`: for each file, `HEAD` for `content-length`; skip if the local size matches; otherwise stream `fetch` to `<file>.part` and rename when complete; print percent progress on one line. Then call `buildDb` with a progress printer and print the returned counts and elapsed time.
- [ ] **Step 2:** Run `node build.js`. Expected: finishes, prints about 308,129 + stubs nodes and about 8.43 million edges.
- [ ] **Step 3:** Sanity-check against the dataset's own numbers:

```bash
node -e "const {open,neighborhood}=require('./lib/graphdb');const r=neighborhood(open('data/mathlib.db'),'Eq.refl',{explicit:false});console.log(r.focus.in_degree,r.in.totals)"
```
Expected: `69579 [ N ]` with N within 1% of 69,579 (the dataset's `in_degree` is computed on the deduplicated graph). Also time it: under 1 second.
- [ ] **Step 4:** Write `README.md`: requirements, `node build.js`, `node server.js`, the URL, and how to run tests.

### Task 5: The page

**Files:**
- Modify: `public/index.html`

**Interfaces:**
- Consumes: the two API endpoints.

Behaviour (the builder chooses spacing, colours and markup):

- **Top bar:** search box with a dropdown of results (debounced 150 ms, arrow keys + Enter, `/` focuses it); "explicit only" checkbox (checked by default); depth buttons 1 / 2 / 3; per-side cap selector 25 / 50 / 100.
- **State in the URL hash:** `#n=<encoded name>&d=1&e=1&l=25`. Changing focus pushes a history entry, so browser back/forward walks visited nodes. Loading with no hash shows the search box and a short hint with three example names (`Nat.add_comm`, `Real.sqrt_nonneg`, `Commute.exp_right`).
- **Graph:** SVG. Focus in the centre column; dependencies in columns to the left (distance 1 nearest), dependents in columns to the right. Within a column, nodes are ordered by pagerank. Each node is a labelled pill coloured by `kind`, with the label shortened in the middle when long and the full name in a tooltip. Edges are curved lines between adjacent or same-side nodes; synthesized edges are dashed and fainter. Arrowheads point from the dependent to the dependency. The SVG pans by drag and zooms by wheel.
- **Column headers:** "depends on (shown / total)" and "used by (shown / total)" from `totals`; when capped, say so ("top 25 of 69,579 by PageRank").
- **Interaction:** hover highlights a node and its edges; click refocuses on it.
- **Side panel:** focused node's full name (copy button), kind, module, file module, in/out degree, PageRank, DAG layer (`in a cycle` when −1), tactic proof / count / top tactic, instance class, additive pair (as a link that refocuses). Stub nodes show "no metadata in dataset". A link to the Mathlib docs search for the name.
- **Empty and error states:** "No dependencies with explicit edges only — try turning the filter off" when a side is empty and the filter is on; a visible message when the API returns 404 or the server is unreachable.
- Works in light and dark colour schemes (`prefers-color-scheme`).

- [ ] **Step 1:** Implement the page.
- [ ] **Step 2:** Start `node server.js`, open `http://127.0.0.1:5173/#n=Commute.exp_right`, and check in a browser: both sides render; clicking a node refocuses and back returns; the explicit toggle and depth 3 work; `Eq.refl` loads quickly and shows the capped message; a stub node and an unknown name show their messages; no console errors.
