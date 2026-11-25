const fs = require('node:fs');
const readline = require('node:readline');

// Split one CSV line into fields (RFC 4180 quoting; no embedded newlines).
function parseLine(line) {
  if (!line.includes('"')) return line.split(',');
  const out = [];
  let field = '';
  let quoted = false;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (quoted) {
      if (c === '"') {
        if (line[i + 1] === '"') {
          field += '"';
          i++;
        } else quoted = false;
      } else field += c;
    } else if (c === '"') quoted = true;
    else if (c === ',') {
      out.push(field);
      field = '';
    } else field += c;
  }
  out.push(field);
  return out;
}

// Yields each data row as an array of fields; the header row is skipped.
async function* records(path) {
  const rl = readline.createInterface({ input: fs.createReadStream(path), crlfDelay: Infinity });
  let first = true;
  for await (const line of rl) {
    if (first) {
      first = false;
      continue;
    }
    if (line) yield parseLine(line);
  }
}

// Yields each data row as an object keyed by the header.
async function* rows(path) {
  const rl = readline.createInterface({ input: fs.createReadStream(path), crlfDelay: Infinity });
  let header = null;
  for await (const line of rl) {
    if (!header) {
      header = parseLine(line);
      continue;
    }
    if (!line) continue;
    const fields = parseLine(line);
    const row = {};
    for (let i = 0; i < header.length; i++) row[header[i]] = fields[i] ?? '';
    yield row;
  }
}

module.exports = { parseLine, records, rows };
