const fs = require('node:fs');
const path = require('node:path');

// Finds a declaration's statement in Lean 4 source text. This is a line-based heuristic,
// not a Lean parser: it follows namespaces and reads up to the `:=` that ends the signature.

const KEYWORDS = 'theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom';
const MODIFIERS = 'private|protected|noncomputable|unsafe|partial|nonrec|public|scoped|local|meta';
const DECL = new RegExp(
  `^\\s*((?:@\\[[^\\]]*\\]\\s*)*)((?:(?:${MODIFIERS})\\s+)*)(${KEYWORDS})\\s+(?:\\(priority[^)]*\\)\\s*)?([^\\s:({\\[⦃]+)`
);
const SECTION = new RegExp(`^(?:@\\[[^\\]]*\\]\\s*)?(?:(?:${MODIFIERS})\\s+)*(section|mutual)\\b`);
const ANY_DECL = new RegExp(`^(?:@\\[[^\\]]*\\]\\s*)*(?:(?:${MODIFIERS})\\s+)*(?:${KEYWORDS}|alias|example|namespace|section|end|variable|open|universe)\\b`);
const BLOCK_KINDS = new Set(['structure', 'class', 'inductive']);
const OPEN = '([{⦃⟨', CLOSE = ')]}⦄⟩';
const MAX_LINES = 60;

// 'Mathlib.Data.Real.Sqrt' -> 'Mathlib/Data/Real/Sqrt.lean'; null for anything else.
function modulePath(module) {
  if (typeof module !== 'string' || !/^Mathlib(\.[\p{L}\p{N}_']+)+$/u.test(module)) return null;
  return module.split('.').join('/') + '.lean';
}

// Private declarations are stored as `_private.<module>.0.<name>`.
const publicName = (name) => name.replace(/^_private\..*?\.0\./, '');

// The signature: from the declaration line up to the top-level `:=`, or to the first
// pattern-matching case, or (for instances) to `where`. `rest` is where the body starts
// ([line index, column]), or null when the declaration has none.
function signature(lines, start, kind) {
  const out = [];
  const done = (rest = null) => ({ text: out.join('\n').trimEnd(), rest });
  if (BLOCK_KINDS.has(kind)) {
    for (let i = start; i < lines.length && out.length < MAX_LINES; i++) {
      if (!lines[i].trim() || (i > start && ANY_DECL.test(lines[i]))) break;
      const cut = lines[i].indexOf(':=');
      if (cut >= 0 && i === start && !/\bwhere\b/.test(lines[i])) { // `class Foo := ...` shorthand
        out.push(lines[i].slice(0, cut));
        return done([i, cut]);
      }
      out.push(lines[i]);
    }
    return done();
  }
  let depth = 0;
  for (let i = start; i < lines.length && out.length < MAX_LINES; i++) {
    const line = lines[i];
    if (i > start && (!line.trim() || ANY_DECL.test(line))) break;
    if (i > start && depth === 0 && line.trimStart().startsWith('|')) return done([i, 0]);
    let end = -1;
    for (let c = 0; c < line.length; c++) {
      const ch = line[c];
      if (OPEN.includes(ch)) depth++;
      else if (CLOSE.includes(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && ch === ':' && line[c + 1] === '=') { end = c; break; }
      else if (depth === 0 && ch === '-' && line[c + 1] === '-') break; // line comment
    }
    if (end >= 0) {
      out.push(line.slice(0, end));
      return done([i, end]);
    }
    const where = depth === 0 ? /\swhere\s*$/.exec(line) : null;
    if (where) {
      out.push(line.slice(0, where.index));
      return done([i, where.index + 1]);
    }
    out.push(line);
  }
  return done();
}

// The proof or definition: everything from `rest` to the next command. Body lines are
// indented, so the next unindented line ends it (except the few that continue a declaration).
const CONTINUES = /^(termination_by|decreasing_by|where|deriving)\b|^[|)\]}⟩]/;
function bodyText(lines, [line, col]) {
  let end = line + 1;
  while (end < lines.length && (!lines[end].trim() || /^\s/.test(lines[end]) || CONTINUES.test(lines[end]))) end++;
  const out = [lines[line].slice(col), ...lines.slice(line + 1, end)];
  while (out.length && !out[out.length - 1].trim()) out.pop();
  return out.join('\n').trimEnd() || null;
}

// Attribute lines and the docstring sitting directly above line `start`.
function preamble(lines, start) {
  let i = start;
  while (i > 0 && /^\s*@\[.*\]\s*$/.test(lines[i - 1])) i--;
  const attrs = lines.slice(i, start);
  let doc = null;
  if (i > 0 && /-\/\s*$/.test(lines[i - 1])) {
    let j = i - 1;
    while (j >= 0 && !lines[j].includes('/--') && i - j < 200) j--;
    if (j >= 0 && lines[j].includes('/--')) {
      doc = lines.slice(j, i).join('\n').replace(/^[\s\S]*?\/--/, '').replace(/-\/\s*$/, '')
        .split('\n').map((l) => l.trim()).join('\n').trim();
    }
  }
  return { attrs, doc };
}

// Scans a file once and returns { find(fullName) }. `find` gives
// { statement, body, context, doc, line } or null. `context` is the binder text of the
// `variable` commands in scope, which the statement may use without declaring; `line` is
// 1-based, of the declaration keyword.
function indexSource(source) {
  const lines = String(source || '').split(/\r?\n/);
  const scopes = []; // namespace name, or null for a section
  const variables = [[]]; // per open scope (the file first): binder text of its `variable` commands
  const byName = new Map(); // resolved name -> [line index, keyword, context]; the first declaration wins
  const suffixable = new Map(); // the same, without declarations written `_root_.…`
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.startsWith('namespace ')) { scopes.push(line.slice(10).trim().split(/\s/)[0]); variables.push([]); continue; }
    if (SECTION.test(line)) { scopes.push(null); variables.push([]); continue; }
    if (/^end\b/.test(line)) { scopes.pop(); if (variables.length > 1) variables.pop(); continue; }
    if (/^variable\b/.test(line)) {
      let text = line.slice(8), j = i + 1;
      while (j < lines.length && /^\s+\S/.test(lines[j])) text += ' ' + lines[j++].trim();
      text = text.trim().replace(/\s+/g, ' ');
      if (!/\sin$/.test(text)) variables[variables.length - 1].push(text); // `variable … in` covers one command only
      continue;
    }
    const m = DECL.exec(line);
    if (!m) continue;
    const kind = m[3], declared = m[4];
    const rooted = declared.startsWith('_root_.');
    const ns = scopes.filter(Boolean).join('.');
    const resolved = rooted ? declared.slice(7) : ns ? `${ns}.${declared}` : declared;
    const entry = [i, kind, variables.flat().join(' ')];
    if (!byName.has(resolved)) byName.set(resolved, entry);
    if (!rooted && !suffixable.has(resolved)) suffixable.set(resolved, entry);
  }
  const build = ([i, kind, context]) => {
    const { attrs, doc } = preamble(lines, i);
    const sig = signature(lines, i, kind);
    const body = sig.rest ? bodyText(lines, sig.rest) : null;
    return { statement: [...attrs, sig.text].join('\n'), body, context, doc, line: i + 1 };
  };
  return {
    find(fullName) {
      if (!fullName) return null;
      const target = publicName(String(fullName));
      if (byName.has(target)) return build(byName.get(target));
      // A namespace this scan did not follow: accept a declaration whose name is a suffix
      // of the one asked for, the longest such suffix first.
      for (let dot = target.indexOf('.'); dot >= 0; dot = target.indexOf('.', dot + 1)) {
        const entry = suffixable.get(target.slice(dot + 1));
        if (entry) return build(entry);
      }
      return null;
    },
  };
}

// One declaration in one file's text.
function findDeclaration(source, fullName) {
  return source && fullName ? indexSource(source).find(fullName) : null;
}

// A file that moved leaves a shim behind: its imports plus `deprecated_module`.
// Returns the paths such a shim points to, or [] for an ordinary file.
function redirects(source) {
  if (!/^deprecated_module\b/m.test(source || '')) return [];
  const out = [];
  for (const m of source.matchAll(/^(?:public\s+)?import\s+(\S+)/gm)) {
    const p = modulePath(m[1]);
    if (p) out.push(p);
  }
  return out;
}

// Finds `name` starting from the file at `filePath`, following a moved file through its
// deprecation shim. `read(path)` resolves to the file's text, or null when there is none;
// `indexOf(path, text)` may supply a cached index. Returns the declaration with the `path`
// it was found in, or { missing: 'file_missing' | 'not_in_file' }.
const MAX_FILES_PER_LOOKUP = 6;
async function locate(read, filePath, name, indexOf = (_path, text) => indexSource(text)) {
  const queue = [filePath];
  const seen = new Set(queue);
  let first = true;
  while (queue.length && seen.size <= MAX_FILES_PER_LOOKUP) {
    const current = queue.shift();
    const text = await read(current);
    if (text === null && first) return { missing: 'file_missing' };
    first = false;
    if (text === null) continue;
    const decl = indexOf(current, text).find(name);
    if (decl) return { ...decl, path: current };
    for (const next of redirects(text)) {
      if (!seen.has(next)) { seen.add(next); queue.push(next); }
    }
  }
  return { missing: 'not_in_file' };
}

// Reads source files from a local checkout of Mathlib: `read(path)` gives the text, or null
// when the file is not there (or the path would leave the checkout).
function localSource(dir) {
  const root = path.resolve(dir);
  return async (filePath) => {
    const full = path.resolve(root, filePath);
    if (!full.startsWith(root + path.sep)) return null;
    try {
      return await fs.promises.readFile(full, 'utf8');
    } catch {
      return null;
    }
  };
}

module.exports = { findDeclaration, indexSource, locate, localSource, modulePath, redirects };
