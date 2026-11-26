// Downloads the MathlibGraph files from Hugging Face, clones Mathlib's source, and builds data/mathlib.db.
const fs = require('node:fs');
const path = require('node:path');
const { Readable } = require('node:stream');
const { pipeline } = require('node:stream/promises');
const { execFileSync } = require('node:child_process');
const { buildDb } = require('./lib/graphdb');

const BASE = 'https://huggingface.co/datasets/CloK-Lab/MathlibGraph/resolve/main/';
const DATA = path.join(__dirname, 'data');
const FILES = [
  { remote: 'v2/declaration/metrics.csv', local: 'metrics.csv' },
  { remote: 'mathlib_edges.csv', local: 'mathlib_edges.csv' },
];

const MATHLIB = 'https://github.com/leanprover-community/mathlib4';
const SOURCE = path.join(DATA, 'mathlib4');

// A shallow clone of Mathlib's current master: the statements shown in the graph are read
// from it. Returns the checkout's folder, or null when it could not be made (the app then
// works without statements in the nodes).
function cloneMathlib() {
  if (fs.existsSync(path.join(SOURCE, 'Mathlib'))) {
    console.log('mathlib4: already cloned (delete data/mathlib4 and run again to refresh it)');
    return SOURCE;
  }
  console.log('mathlib4: cloning the source (about 150 MB)…');
  try {
    fs.rmSync(SOURCE, { recursive: true, force: true });
    execFileSync('git', ['clone', '--depth', '1', '--quiet', MATHLIB, SOURCE], { stdio: 'inherit' });
    return SOURCE;
  } catch (err) {
    console.error(`mathlib4: clone failed (${err.message}). Continuing without statements; is git installed?`);
    return null;
  }
}

const mb = (bytes) => (bytes / 1e6).toFixed(0) + ' MB';
const status = (msg) => process.stdout.write(process.stdout.isTTY ? `\r\x1b[K${msg}` : `${msg}\n`);

async function download({ remote, local }) {
  const dest = path.join(DATA, local);
  const url = BASE + remote;
  const head = await fetch(url, { method: 'HEAD' });
  if (!head.ok) throw new Error(`${remote}: HTTP ${head.status}`);
  const size = Number(head.headers.get('content-length')) || 0;
  if (size && fs.existsSync(dest) && fs.statSync(dest).size === size) {
    console.log(`${local}: already downloaded (${mb(size)})`);
    return dest;
  }
  const res = await fetch(url);
  if (!res.ok || !res.body) throw new Error(`${remote}: HTTP ${res.status}`);
  const part = dest + '.part';
  let got = 0;
  let lastPct = -1;
  const body = Readable.fromWeb(res.body);
  body.on('data', (chunk) => {
    got += chunk.length;
    const pct = size ? Math.floor((got / size) * 100) : 0;
    if (pct !== lastPct && (process.stdout.isTTY || pct % 10 === 0)) {
      lastPct = pct;
      status(`${local}: ${pct}% of ${mb(size)}`);
    }
  });
  await pipeline(body, fs.createWriteStream(part));
  if (size && got !== size) throw new Error(`${local}: got ${got} bytes, expected ${size}`);
  fs.renameSync(part, dest);
  console.log(`${process.stdout.isTTY ? '\r\x1b[K' : ''}${local}: downloaded (${mb(got)})`);
  return dest;
}

async function main() {
  fs.mkdirSync(DATA, { recursive: true });
  const [metricsCsv, edgesCsv] = [await download(FILES[0]), await download(FILES[1])];
  const sourceDir = cloneMathlib();
  const started = Date.now();
  const res = await buildDb({
    sourceDir: sourceDir || undefined,
    edgesCsv,
    metricsCsv,
    dbPath: path.join(DATA, 'mathlib.db'),
    onProgress: ({ phase, rows }) =>
      status(phase === 'index' ? 'building indexes…' : phase === 'reach' ? 'counting indirect dependents…'
        : phase === 'statements' ? `reading statements: ${rows.toLocaleString('en-US')} declarations`
        : `loading ${phase}: ${rows.toLocaleString('en-US')} rows`),
  });
  const n = (v) => v.toLocaleString('en-US');
  console.log(
    `${process.stdout.isTTY ? '\r\x1b[K' : ''}data/mathlib.db: ${n(res.nodes)} declarations ` +
      `(${n(res.stubs)} without metadata), ${n(res.edges)} edges, ${n(res.statements)} statements, ` +
      `${((Date.now() - started) / 1000).toFixed(0)}s`
  );
}

main().catch((err) => {
  console.error(`\nBuild failed: ${err.message}`);
  process.exit(1);
});
