// Statements as Lean itself understands them: every type inferred, every implicit variable
// written out. A Lean process (lean/Signatures.lean) is kept running and asked about
// declarations as they come up; its answers are remembered in a small database of their own,
// so each declaration costs Lean time once, and the answers survive a rebuild of the graph.

const { spawn } = require('node:child_process');
const readline = require('node:readline');
const { DatabaseSync } = require('node:sqlite');

const KEYWORD = { theorem: 'theorem', definition: 'def', abbrev: 'abbrev', opaque: 'def', axiom: 'axiom' };

// Lean prints "Full.name binders : type". The page's converter reads source-style statements,
// "theorem name binders : type", so give it the keyword and the name as the source would
// write it. Null when the kind is not one the converter renders, or the text is not about `name`.
function statementFrom(name, kind, signature) {
  const keyword = KEYWORD[kind];
  const text = String(signature || '').replace(/\s+/g, ' ').trim();
  if (!keyword || !text.startsWith(name)) return null;
  const rest = text.slice(name.length).replace(/^\.\{[^}]*\}/, ''); // universe parameters, if printed
  if (rest && !/^[\s:]/.test(rest)) return null; // a longer name that merely starts the same way
  return `${keyword} ${name.slice(name.lastIndexOf('.') + 1)}${rest}`;
}

class LeanStatements {
  // `command` and `args` start the Lean process (in `cwd`); without a command there is no
  // Lean and only remembered answers are given. `cachePath` is where answers are kept.
  constructor({ cachePath, command, args = [], cwd, env }) {
    this.launch = command ? { command, args, cwd, env } : null;
    this.state = command ? 'idle' : 'off'; // off | idle | starting | ready
    this.child = null;
    this.ready = null; // promise of the running process being ready
    this.waiting = []; // questions sent and not yet answered, oldest first
    this.exited = Promise.resolve();
    this.db = new DatabaseSync(cachePath);
    this.db.exec('CREATE TABLE IF NOT EXISTS signatures(name TEXT PRIMARY KEY, signature TEXT)'); // NULL: Lean has none
    this.read = this.db.prepare('SELECT signature FROM signatures WHERE name = ?');
    this.write = this.db.prepare('INSERT OR REPLACE INTO signatures(name, signature) VALUES (?, ?)');
  }

  // Remembered statements for `names` that are also in `kinds` ({ name: kind }), or, when
  // `kinds` is left out, the raw signatures. Never starts or waits for Lean.
  cached(names, kinds) {
    const out = {};
    for (const name of names) {
      const row = this.read.get(name);
      if (!row || row.signature === null) continue;
      const value = kinds ? statementFrom(name, kinds[name], row.signature) : statementFrom(name, 'theorem', row.signature);
      if (value) out[name] = value;
    }
    return out;
  }

  // Statements for `decls` ([{ name, kind }]): remembered ones at once, the others asked of
  // Lean when it is available. Resolves to { name: statement }; declarations Lean does not
  // know, or cannot be asked about, are simply absent.
  async statements(decls) {
    const out = {}, unknown = [];
    for (const d of decls) {
      const row = this.read.get(d.name);
      if (!row) { if (!/[\r\n]/.test(d.name)) unknown.push(d); continue; }
      const value = row.signature === null ? null : statementFrom(d.name, d.kind, row.signature);
      if (value) out[d.name] = value;
    }
    if (!unknown.length || this.state === 'off') return out;
    const replies = await this.ask(unknown.map((d) => d.name));
    unknown.forEach((d, k) => {
      const reply = replies[k];
      if (!reply) return; // Lean went away before answering: ask again another time
      this.write.run(d.name, typeof reply.signature === 'string' ? reply.signature : null);
      const value = statementFrom(d.name, d.kind, reply.signature);
      if (value) out[d.name] = value;
    });
    return out;
  }

  // Sends `names` to Lean and resolves to its replies in the same order (null where Lean
  // stopped before answering).
  async ask(names) {
    if (!(await this.start())) return names.map(() => null);
    return Promise.all(names.map((name) => new Promise((resolve) => {
      this.waiting.push(resolve);
      this.child.stdin.write(name + '\n');
    })));
  }

  // Starts the Lean process if it is not running; resolves to whether it is ready.
  start() {
    if (this.state === 'off') return Promise.resolve(false);
    if (this.ready) return this.ready;
    this.state = 'starting';
    const { command, args, cwd, env } = this.launch;
    const child = spawn(command, args, { cwd, env, stdio: ['pipe', 'pipe', 'pipe'] });
    this.child = child;
    let becameReady = false, settle;
    this.ready = new Promise((resolve) => { settle = resolve; });
    this.lastError = '';
    child.stderr.on('data', (chunk) => { this.lastError = (this.lastError + chunk).slice(-2000); });
    child.stdin.on('error', () => {}); // a write to a process that just died: its exit handles the rest
    readline.createInterface({ input: child.stdout }).on('line', (line) => {
      let reply;
      try { reply = JSON.parse(line); } catch { return; } // not ours: Lean chatter
      if (reply && reply.ready) { becameReady = true; this.state = 'ready'; settle(true); return; }
      const answer = this.waiting.shift();
      if (answer) answer(reply);
    });
    this.exited = new Promise((resolve) => {
      const gone = () => {
        if (this.child !== child) return resolve();
        this.child = null;
        this.ready = null;
        // A process that never got ready will not do better next time; one that died later may.
        this.state = becameReady && this.launch ? 'idle' : 'off';
        settle(false);
        for (const answer of this.waiting.splice(0)) answer(null);
        resolve();
      };
      child.on('error', gone);
      child.on('exit', gone);
    });
    return this.ready;
  }

  // Stops Lean and closes the cache.
  async close() {
    this.launch = null;
    if (this.child) {
      this.child.stdin.end();
      this.child.kill();
    }
    await this.exited;
    this.state = 'off';
    this.db.close();
  }
}

module.exports = { LeanStatements, statementFrom };
