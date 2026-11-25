// How many declarations depend on each one, directly or through others ("reach").
//
// Each node carries the set of everything that uses it. Sets are passed down the edges
// until nothing changes, which also settles cycles. A set is kept exactly while it is
// small; beyond SMALL elements it becomes a HyperLogLog sketch, so large counts are
// estimates (a few percent off) and small ones, including zero, are exact.

const P = 10, M = 1 << P; // sketch size: 1024 registers, about 3% typical error
const SMALL = 128;
const ALPHA = 0.7213 / (1 + 1.079 / M);
const POW = Float64Array.from({ length: 40 }, (_, k) => 2 ** -k);

// A well-mixed 32-bit hash of a node number (the murmur3 finaliser).
function hash(x) {
  x = Math.imul(x ^ (x >>> 16), 0x85ebca6b);
  x = Math.imul(x ^ (x >>> 13), 0xc2b2ae35);
  return (x ^ (x >>> 16)) >>> 0;
}

// Records one element in a sketch; returns true if the sketch changed.
function add(registers, element) {
  const h = hash(element + 1);
  const index = h >>> (32 - P);
  const rest = (h << P) >>> 0;
  const rank = rest === 0 ? 32 - P + 1 : Math.clz32(rest) + 1;
  if (registers[index] >= rank) return false;
  registers[index] = rank;
  return true;
}

function estimate(registers) {
  let sum = 0, zeros = 0;
  for (let j = 0; j < M; j++) {
    sum += POW[registers[j]];
    if (registers[j] === 0) zeros++;
  }
  const raw = (ALPHA * M * M) / sum;
  return raw <= 2.5 * M && zeros > 0 ? M * Math.log(M / zeros) : raw;
}

// `src[e]` depends on `dst[e]`, both node numbers in 0 … n-1. `order` is the order to
// visit nodes in; visiting users before what they use makes one pass enough.
// Returns a Uint32Array: for each node, how many others depend on it at any distance.
function computeReach(n, src, dst, order) {
  // Edges grouped by source: uses[start[u] … start[u+1]) are what u depends on.
  const start = new Uint32Array(n + 1);
  for (let e = 0; e < src.length; e++) start[src[e] + 1]++;
  for (let u = 0; u < n; u++) start[u + 1] += start[u];
  const uses = new Int32Array(src.length);
  const fill = start.slice(0, n);
  for (let e = 0; e < src.length; e++) uses[fill[src[e]]++] = dst[e];

  const exact = Array.from({ length: n }, (_, v) => new Set([v])); // a node's users, itself included
  const sketch = new Array(n).fill(null); // set once the exact set has grown too large
  const promote = (v) => {
    const registers = new Uint8Array(M);
    for (const x of exact[v]) add(registers, x);
    sketch[v] = registers;
    exact[v] = null;
  };
  // Adds everything that uses u to v's users; returns true if v's set grew.
  const merge = (u, v) => {
    let changed = false;
    if (exact[u] && exact[v]) {
      const into = exact[v], before = into.size;
      for (const x of exact[u]) into.add(x);
      changed = into.size > before;
      if (into.size > SMALL) promote(v);
      return changed;
    }
    if (exact[v]) promote(v);
    const into = sketch[v];
    if (exact[u]) {
      for (const x of exact[u]) if (add(into, x)) changed = true;
    } else {
      const from = sketch[u];
      for (let j = 0; j < M; j++) if (from[j] > into[j]) { into[j] = from[j]; changed = true; }
    }
    return changed;
  };

  const visit = order || Uint32Array.from({ length: n }, (_, v) => v);
  const dirty = new Uint8Array(n).fill(1);
  for (let again = true; again; ) {
    again = false;
    for (let k = 0; k < visit.length; k++) {
      const u = visit[k];
      if (!dirty[u]) continue;
      dirty[u] = 0;
      for (let e = start[u]; e < start[u + 1]; e++) {
        const v = uses[e];
        if (v !== u && merge(u, v)) { dirty[v] = 1; again = true; }
      }
    }
  }

  const out = new Uint32Array(n);
  for (let v = 0; v < n; v++) out[v] = Math.max(0, (exact[v] ? exact[v].size : Math.round(estimate(sketch[v]))) - 1);
  return out;
}

module.exports = { computeReach };
