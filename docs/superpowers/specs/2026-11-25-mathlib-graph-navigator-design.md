# Mathlib graph navigator — design

## Intent

Look up one Mathlib theorem or lemma and walk its dependencies in both
directions: what it depends on (out) and what depends on it (in).
Data: `CloK-Lab/MathlibGraph` on Hugging Face (Mathlib commit `534cf0b`,
308,129 declarations, 8,436,366 edges).

## Goals

- Search a declaration by name and focus on it.
- Show its dependencies (left) and its dependents (right), both treated
  equally; click any node to refocus on it.
- Default to explicit edges only (`is_explicit`), with a toggle to include
  the 74% of edges that are synthesized typeclass plumbing.
- Expand either side to depth 1–3.
- Side panel with the focused node's kind, module, in/out degree, PageRank,
  DAG layer, tactic info.
- Back/forward through visited nodes; focus is in the URL so it can be bookmarked.

## Non-goals

- A whole-graph map, or module/namespace level views.
- Hosting or sharing; this runs locally.
- Showing Lean source or proof text (not in the dataset).

## Anti-goals

- Hairballs: a side with too many nodes is capped (top N by PageRank, with
  "show more") rather than drawn in full. `Eq.refl` has 69,579 dependents.

## Approaches

1. **Local app: SQLite + small Node.js server + one HTML page (picked by
   the user).** Instant lookups in both
   directions, metrics available, least work. Local only.
2. Static site with packed binary adjacency files. Shareable by link, more
   work, weaker name search. Can be added later from the same build script.
3. Query Hugging Face live. No download, but seconds per click and fragile.

## How (Claude's calls)

- Node.js (user's choice), version 22+, no npm dependencies: built-in
  `node:sqlite`, `node:http`, `node:test`.
- `build.js`: downloads `mathlib_edges.csv` and `v2/declaration/metrics.csv`
  into `data/`, builds `data/mathlib.db`. Nodes get integer ids; edges are
  stored as `(src, dst, explicit)` with indexes on both directions; self-loops
  dropped.
- `server.js`: built-in HTTP server. `GET /api/search?q=`,
  `GET /api/node?name=&depth=&explicit=&limit=`, and the static page.
- `index.html`: single page, no build step, SVG layered layout drawn by hand
  (columns by distance from the focus), no graph library.
- Search: prefix and substring match on name, ranked by PageRank.

## Left to the builder

Exact caps, colours (by kind), layout spacing, keyboard shortcuts.
