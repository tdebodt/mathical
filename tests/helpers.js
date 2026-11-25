const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { buildDb } = require('../lib/graphdb');

const fixtures = path.join(__dirname, 'fixtures');

async function buildFixtureDb() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'mathical-'));
  const dbPath = path.join(dir, 'test.db');
  const res = await buildDb({
    edgesCsv: path.join(fixtures, 'edges.csv'),
    metricsCsv: path.join(fixtures, 'metrics.csv'),
    dbPath,
  });
  return { dbPath, res };
}

module.exports = { buildFixtureDb, fixtures };
