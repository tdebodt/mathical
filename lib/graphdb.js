const fs = require('node:fs');
const { DatabaseSync } = require('node:sqlite');
const { records, rows } = require('./csv');
const { computeReach } = require('./reach');
const { indexSource, locate, localSource, modulePath } = require('./leansource');

const SCHEMA = `
CREATE TABLE nodes(
  id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, kind TEXT, module TEXT,
  file_module TEXT, in_degree INT, out_degree INT, pagerank REAL DEFAULT 0,
  dag_layer INT, is_tactic_proof INT, tactic_count INT, top_tactic TEXT,
  is_instance INT, instance_class TEXT, to_additive_pair TEXT,
  reach INT, -- how many declarations depend on this one, directly or indirectly (see lib/reach.js)
  statement TEXT, context TEXT, doc TEXT, -- from the Lean source, when a checkout was given (see lib/leansource.js)
  body TEXT, -- what follows the statement, kept for abbreviations only: what the short name stands for
  parent TEXT); -- for X.toY where Y is a structure that X extends: the full name of Y
CREATE TABLE edges(src INT NOT NULL, dst INT NOT NULL, explicit INT NOT NULL,
  PRIMARY KEY(src,dst)) WITHOUT ROWID;
`;

const BATCH = 200_000;

const text = (v) => (v === '' || v === undefined ? null : v);
const num = (v) => (v === '' || v === undefined ? null : Number(v));
const bool = (v) => (v === '' || v === undefined ? null : v === 'True' ? 1 : 0);

// Loads the two CSVs into a fresh SQLite file. An edge (src, dst) means src depends on dst.
async function buildDb({ edgesCsv, metricsCsv, dbPath, sourceDir, onProgress = () => {} }) {
  const tmp = dbPath + '.tmp';
  fs.rmSync(tmp, { force: true });
  const db = new DatabaseSync(tmp);
  try {
    db.exec('PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; PRAGMA cache_size=-262144;');
    db.exec(SCHEMA);

    const ids = new Map();
    const insertNode = db.prepare(
      `INSERT INTO nodes(id, name, kind, module, file_module, in_degree, out_degree, pagerank,
         dag_layer, is_tactic_proof, tactic_count, top_tactic, is_instance, instance_class,
         to_additive_pair) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)`
    );
    const insertStub = db.prepare('INSERT INTO nodes(id, name) VALUES (?, ?)');
    const insertEdge = db.prepare('INSERT OR IGNORE INTO edges(src, dst, explicit) VALUES (?,?,?)');

    const kinds = new Map(); // name -> kind
    const layers = []; // dag_layer by node id - 1: 0 for results nothing uses, higher for foundations
    let n = 0;
    db.exec('BEGIN');
    for await (const r of rows(metricsCsv)) {
      if (!r.name || ids.has(r.name)) continue;
      const id = ids.size + 1;
      ids.set(r.name, id);
      layers[id - 1] = num(r.dag_layer) ?? -1;
      kinds.set(r.name, r.kind);
      insertNode.run(
        id, r.name, text(r.kind), text(r.module), text(r.file_module), num(r.in_degree),
        num(r.out_degree), num(r.pagerank) ?? 0, num(r.dag_layer), bool(r.is_tactic_proof),
        num(r.tactic_count), text(r.top_tactic), bool(r.is_instance), text(r.instance_class),
        text(r.to_additive_pair)
      );
      if (++n % BATCH === 0) onProgress({ phase: 'nodes', rows: n });
    }
    db.exec('COMMIT');
    onProgress({ phase: 'nodes', rows: n });

    // `Semiring.toNonAssocSemiring` says that every semiring is a non-associative semiring.
    // Such a projection is recognised by its target being a structure: `Equiv.toFun` is a
    // field, because nothing called `Fun` exists.
    const setParent = db.prepare('UPDATE nodes SET parent = ? WHERE id = ?');
    db.exec('BEGIN');
    for (const [name, kind] of kinds) {
      if (kind !== 'abbrev' && kind !== 'definition') continue;
      const m = /^(.+)\.to([A-Z][^.]*)$/.exec(name);
      if (!m) continue;
      const scope = m[1].split('.');
      for (let k = scope.length - 1; k >= 0; k--) {
        const candidate = [...scope.slice(0, k), m[2]].join('.');
        if (kinds.get(candidate) === 'inductive') { setParent.run(candidate, ids.get(name)); break; }
      }
    }
    db.exec('COMMIT');

    let stubs = 0;
    const idOf = (name) => {
      let id = ids.get(name);
      if (id === undefined) {
        id = ids.size + 1;
        ids.set(name, id);
        insertStub.run(id, name);
        stubs++;
      }
      return id;
    };

    let edges = 0;
    const from = [], to = []; // every edge again, by node id - 1, for the reach computation
    n = 0;
    db.exec('BEGIN');
    for await (const f of records(edgesCsv)) {
      if (++n % BATCH === 0) {
        db.exec('COMMIT; BEGIN');
        onProgress({ phase: 'edges', rows: n });
      }
      if (f.length < 3 || !f[0] || !f[1] || f[0] === f[1]) continue;
      const s = idOf(f[0]), d = idOf(f[1]);
      edges += Number(insertEdge.run(s, d, f[2] === 'True' ? 1 : 0).changes);
      from.push(s - 1);
      to.push(d - 1);
    }
    db.exec('COMMIT');
    onProgress({ phase: 'edges', rows: n });

    onProgress({ phase: 'reach', rows: ids.size });
    const count = ids.size;
    // Visit results before the foundations they rest on, so that one pass nearly suffices.
    const order = Uint32Array.from({ length: count }, (_, v) => v).sort((a, b) => (layers[a] ?? -1) - (layers[b] ?? -1));
    const reach = computeReach(count, Int32Array.from(from), Int32Array.from(to), order);
    const setReach = db.prepare('UPDATE nodes SET reach = ? WHERE id = ?');
    db.exec('BEGIN');
    for (let v = 0; v < count; v++) setReach.run(reach[v], v + 1);
    db.exec('COMMIT');

    const statements = sourceDir ? await storeStatements(db, sourceDir, onProgress) : 0;

    onProgress({ phase: 'index', rows: edges });
    db.exec('CREATE INDEX edges_dst ON edges(dst, src); ANALYZE;');
    db.close();
    fs.renameSync(tmp, dbPath);
    return { nodes: ids.size, edges, stubs, statements };
  } catch (err) {
    try {
      db.close();
    } catch {}
    fs.rmSync(tmp, { force: true });
    throw err;
  }
}

// Reads every declaration's statement, the `variable` context it is written in and its
// docstring from a checkout of Mathlib, and stores them on its node. Returns how many were found.
async function storeStatements(db, sourceDir, onProgress) {
  const read = localSource(sourceDir);
  const indexes = new Map(); // a few recently used files, indexed once each
  const indexOf = (filePath, text) => {
    if (!indexes.has(filePath)) {
      if (indexes.size >= 64) indexes.delete(indexes.keys().next().value);
      indexes.set(filePath, indexSource(text));
    }
    return indexes.get(filePath);
  };
  const rows = db.prepare('SELECT id, name, file_module FROM nodes WHERE file_module IS NOT NULL ORDER BY file_module').all();
  const store = db.prepare('UPDATE nodes SET statement = ?, context = ?, doc = ?, body = ? WHERE id = ?');
  const isAbbrev = /^(?:@\[[\s\S]*?\]\s*)*(?:[a-z]+\s+)*?abbrev\s/;
  let found = 0, done = 0;
  db.exec('BEGIN');
  for (const row of rows) {
    if (++done % 20000 === 0) onProgress({ phase: 'statements', rows: done });
    const filePath = modulePath(row.file_module);
    if (!filePath) continue;
    const decl = await locate(read, filePath, row.name, indexOf);
    if (decl.missing) continue;
    const body = decl.body && decl.body.length <= 400 && isAbbrev.test(decl.statement) ? decl.body : null;
    store.run(decl.statement, decl.context || null, decl.doc, body, row.id);
    found++;
  }
  db.exec('COMMIT');
  onProgress({ phase: 'statements', rows: done });
  return found;
}

function open(dbPath) {
  return new DatabaseSync(dbPath, { readOnly: true });
}

const clamp = (v, lo, hi, dflt) => {
  const n = Math.trunc(Number(v));
  return Number.isFinite(n) ? Math.min(hi, Math.max(lo, n)) : dflt;
};

// Case-insensitive substring search: exact match first, then prefixes, then the rest, by PageRank.
function search(db, q, limit = 20) {
  q = String(q ?? '').trim();
  if (!q) return [];
  return db
    .prepare(
      `SELECT * FROM nodes WHERE instr(lower(name), lower(?1)) > 0
       ORDER BY lower(name) = lower(?1) DESC, instr(lower(name), lower(?1)) = 1 DESC,
                pagerank DESC, name ASC
       LIMIT ?2`
    )
    .all(q, clamp(limit, 1, 100, 20))
    .map((r) => ({ ...r }));
}

// "Plumbing": declarations from Lean's core library that are logic or notation machinery
// (Eq.mpr, propext, HAdd.hAdd, instOfNatNat …) and that nearly every proof touches. Core
// declarations about actual data (Nat, Int, List …) are not plumbing, and neither is anything
// from Mathlib, which always has a source file. Declarations without metadata are left alone.
const CORE_DATA = ['Nat', 'Int', 'Fin', 'Rat', 'Bool', 'List', 'Array', 'Vector', 'BitVec', 'Option', 'Prod', 'Sum', 'Sigma', 'PSigma',
  'Subtype', 'Function', 'String', 'Char', 'Float', 'UInt8', 'UInt16', 'UInt32', 'UInt64', 'USize', 'Std', 'Batteries'];
// Mathlib's own counterpart is also plumbing: the projection from a structure to one it
// extends (`Semiring.toNonAssocSemiring`), which nearly every algebraic statement passes through.
const PLUMBING = `(n.parent IS NOT NULL OR (n.file_module IS NULL AND n.kind IS NOT NULL AND substr(n.name, 1, instr(n.name || '.', '.') - 1) NOT IN (${CORE_DATA.map((r) => `'${r}'`).join(',')})))`;

// One side of the neighbourhood, breadth-first. `from`/`to` are the edge columns to walk.
// All interpolated values are integers read from the database.
function walk(db, focusId, from, to, depth, explicit, limit, pinIds = [], hidePlumbing = false, theoremsOnly = false) {
  // What a neighbour must satisfy to be shown, beyond being reached.
  const shown = [hidePlumbing && `NOT ${PLUMBING}`, theoremsOnly && `n.kind = 'theorem'`].filter(Boolean).join(' AND ');
  const filter = explicit ? ' AND explicit = 1' : '';
  const nodes = [];
  const totals = [];
  const hidden = []; // per level: how many were left out by the plumbing and theorem filters
  const kept = [focusId];
  const earlier = []; // subqueries for every id found at earlier levels, kept or not
  let frontier = [focusId];
  for (let d = 1; d <= depth; d++) {
    if (!frontier.length) {
      totals.push(0);
      hidden.push(0);
      continue;
    }
    const level = `SELECT ${to} FROM edges WHERE ${from} IN (${frontier.join(',')})${filter}`;
    const reached = `n.id IN (${level}) AND n.id NOT IN (${kept.join(',')})` + earlier.map((s) => ` AND n.id NOT IN (${s})`).join('');
    const where = reached + (shown ? ` AND ${shown}` : '');
    hidden.push(shown ? db.prepare(`SELECT COUNT(*) c FROM nodes n WHERE ${reached} AND NOT coalesce(${shown}, 0)`).get().c : 0);
    totals.push(db.prepare(`SELECT COUNT(*) c FROM nodes n WHERE ${where}`).get().c);
    const found = db
      .prepare(`SELECT n.* FROM nodes n WHERE ${where} ORDER BY n.pagerank DESC, n.name ASC LIMIT ?`)
      .all(limit);
    // Pinned nodes come first at distance 1 and do not count against the cap.
    const pinned = d === 1 && pinIds.length
      ? db.prepare(`SELECT n.* FROM nodes n WHERE n.id IN (${pinIds.join(',')}) AND ${where} ORDER BY n.pagerank DESC, n.name ASC`).all()
      : [];
    const isPinned = new Set(pinned.map((r) => r.id));
    frontier = [];
    for (const r of [...pinned, ...found.filter((f) => !isPinned.has(f.id))]) {
      nodes.push(isPinned.has(r.id) ? { ...r, dist: d, pinned: true } : { ...r, dist: d });
      kept.push(r.id);
      frontier.push(r.id);
    }
    earlier.push(level);
  }
  const list = kept.join(',');
  const edges = db
    .prepare(`SELECT src, dst, explicit FROM edges WHERE src IN (${list}) AND dst IN (${list})${filter}`)
    .all()
    .map((e) => [e.src, e.dst, e.explicit]);
  return { nodes, edges, totals, hidden };
}

const MAX_PINS = 300;

// What `name` depends on (out) and what depends on it (in), to `depth` levels,
// keeping the top `limit` nodes by PageRank at each level. `pin` names direct
// dependencies that must be included whatever their rank. `hidePlumbing` leaves out
// Lean core machinery (see PLUMBING); `theoremsOnly` leaves out everything that is not a
// theorem. `hidden` reports, per level, how many neighbours those two filters left out.
function neighborhood(db, name, { depth = 1, explicit = true, limit = 25, pin = [], hidePlumbing = false, theoremsOnly = false } = {}) {
  const focus = db.prepare('SELECT * FROM nodes WHERE name = ?').get(String(name ?? ''));
  if (!focus) return null;
  depth = clamp(depth, 1, 3, 1);
  limit = clamp(limit, 1, 200, 25);
  const pinNames = (Array.isArray(pin) ? pin : []).filter((p) => typeof p === 'string').slice(0, MAX_PINS);
  const pinIds = pinNames.length
    ? db.prepare(`SELECT id FROM nodes WHERE name IN (${pinNames.map(() => '?').join(',')})`).all(...pinNames).map((r) => r.id)
    : [];
  const pairExists =
    !!focus.to_additive_pair && !!db.prepare('SELECT 1 FROM nodes WHERE name = ?').get(focus.to_additive_pair);
  return {
    focus: { ...focus, pair_exists: pairExists },
    out: walk(db, focus.id, 'src', 'dst', depth, explicit, limit, pinIds, hidePlumbing, theoremsOnly),
    in: walk(db, focus.id, 'dst', 'src', depth, explicit, limit, [], hidePlumbing, theoremsOnly),
  };
}

// Of `names`, the ones that are facts in their own right: theorems that are not plumbing.
// (Used to measure what a proof rests on.) Returns them in the order given.
function facts(db, names) {
  const wanted = [...new Set(names)].slice(0, 5000);
  const real = new Set();
  for (let i = 0; i < wanted.length; i += 500) {
    const chunk = wanted.slice(i, i + 500);
    // Typeclass instances and "every X is a Y" facts are how Lean finds structure, not steps of an argument.
    const glue = `coalesce(n.is_instance, 0) = 1 OR n.name GLOB '*.to[A-Z]*' OR n.name GLOB '*inst[A-Z]*'`;
    for (const row of db.prepare(`SELECT n.name FROM nodes n WHERE n.kind = 'theorem' AND NOT ${PLUMBING} AND NOT (${glue}) AND n.name IN (${chunk.map(() => '?').join(',')})`).all(...chunk)) real.add(row.name);
  }
  return wanted.filter((n) => real.has(n));
}

module.exports = { buildDb, open, search, neighborhood, facts };
