const fs = require('node:fs');
const { DatabaseSync } = require('node:sqlite');
const { records, rows } = require('./csv');

const SCHEMA = `
CREATE TABLE nodes(
  id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, kind TEXT, module TEXT,
  file_module TEXT, in_degree INT, out_degree INT, pagerank REAL DEFAULT 0,
  dag_layer INT, is_tactic_proof INT, tactic_count INT, top_tactic TEXT,
  is_instance INT, instance_class TEXT, to_additive_pair TEXT);
CREATE TABLE edges(src INT NOT NULL, dst INT NOT NULL, explicit INT NOT NULL,
  PRIMARY KEY(src,dst)) WITHOUT ROWID;
`;

const BATCH = 200_000;

const text = (v) => (v === '' || v === undefined ? null : v);
const num = (v) => (v === '' || v === undefined ? null : Number(v));
const bool = (v) => (v === '' || v === undefined ? null : v === 'True' ? 1 : 0);

// Loads the two CSVs into a fresh SQLite file. An edge (src, dst) means src depends on dst.
async function buildDb({ edgesCsv, metricsCsv, dbPath, onProgress = () => {} }) {
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

    let n = 0;
    db.exec('BEGIN');
    for await (const r of rows(metricsCsv)) {
      if (!r.name || ids.has(r.name)) continue;
      const id = ids.size + 1;
      ids.set(r.name, id);
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
    n = 0;
    db.exec('BEGIN');
    for await (const f of records(edgesCsv)) {
      if (++n % BATCH === 0) {
        db.exec('COMMIT; BEGIN');
        onProgress({ phase: 'edges', rows: n });
      }
      if (f.length < 3 || !f[0] || !f[1] || f[0] === f[1]) continue;
      edges += Number(insertEdge.run(idOf(f[0]), idOf(f[1]), f[2] === 'True' ? 1 : 0).changes);
    }
    db.exec('COMMIT');
    onProgress({ phase: 'edges', rows: n });

    onProgress({ phase: 'index', rows: edges });
    db.exec('CREATE INDEX edges_dst ON edges(dst, src); ANALYZE;');
    db.close();
    fs.renameSync(tmp, dbPath);
    return { nodes: ids.size, edges, stubs };
  } catch (err) {
    try {
      db.close();
    } catch {}
    fs.rmSync(tmp, { force: true });
    throw err;
  }
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

// One side of the neighbourhood, breadth-first. `from`/`to` are the edge columns to walk.
// All interpolated values are integers read from the database.
function walk(db, focusId, from, to, depth, explicit, limit, pinIds = []) {
  const filter = explicit ? ' AND explicit = 1' : '';
  const nodes = [];
  const totals = [];
  const kept = [focusId];
  const earlier = []; // subqueries for every id found at earlier levels, kept or not
  let frontier = [focusId];
  for (let d = 1; d <= depth; d++) {
    if (!frontier.length) {
      totals.push(0);
      continue;
    }
    const level = `SELECT ${to} FROM edges WHERE ${from} IN (${frontier.join(',')})${filter}`;
    const where =
      `n.id IN (${level}) AND n.id NOT IN (${kept.join(',')})` +
      earlier.map((s) => ` AND n.id NOT IN (${s})`).join('');
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
  return { nodes, edges, totals };
}

const MAX_PINS = 300;

// What `name` depends on (out) and what depends on it (in), to `depth` levels,
// keeping the top `limit` nodes by PageRank at each level. `pin` names direct
// dependencies that must be included whatever their rank.
function neighborhood(db, name, { depth = 1, explicit = true, limit = 25, pin = [] } = {}) {
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
    out: walk(db, focus.id, 'src', 'dst', depth, explicit, limit, pinIds),
    in: walk(db, focus.id, 'dst', 'src', depth, explicit, limit),
  };
}

module.exports = { buildDb, open, search, neighborhood };
