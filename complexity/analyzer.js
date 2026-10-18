// Static complexity analyzer: walks the language-neutral IR, derives a Big-O bound with explicit rules,
// and throws `Und` ("cannot be determined") whenever a rule's preconditions cannot be checked.
import * as A from './algebra.js';
import { Und, eachExpr, eachStmt, eachStmtExprs, eqE, idsIn, show } from './util.js';
import { Env, installCore, isContainer, MUTATORS, REMOVERS } from './core.js';
import { installExprCost } from './cost-expr.js';
import { installLoops } from './loops.js';
import { installRecursion } from './recursion.js';
import { installMarks } from './marks.js';

const { ONE } = A;
const MAX_CALLS = 600;

export class Analyzer {
  constructor(ir, opts = {}) {
    this.ir = ir;
    this.lang = ir.lang;
    this.opts = opts;
    this.funcs = ir.funcs;
    this.syms = {};
    this.symNames = new Set();
    this.psyms = new Map();
    this.paramSyms = [];
    this.growthPrev = new Map(); this.growthNow = new Map();
    this.callsPrev = new Map(); this.callsNow = new Map(); this.depthPrev = new Map(); this.depthNow = new Map();
    this.assumptions = new Map();
    this.curLine = 0;
    this.stack = [];
  }

  // ------------------------------------------------------------------ small helpers
  assume(text) { if (!this.assumptions.has(text)) this.assumptions.set(text, true); }
  node(kind, line, text, extra = {}) {
    if (!this.recording) return null;
    const n = { kind, line, text, children: [], cost: null, ...extra };
    this.cur.children.push(n);
    return n;
  }
  within(n, f) {
    if (!n) return f();
    const prev = this.cur; this.cur = n;
    try { return f(); } finally { this.cur = prev; }
  }

  /** product of the trip counts of the loops entered after `depth`; a `global` loop entry restarts the product */
  multSince(depth = 0, v = null) {
    let m = ONE;
    const L = this.fr.loops;
    for (let i = depth; i < L.length; i++) {
      const e = L[i];
      if (e.global) {
        // a global entry counts *all* executions, but only once per lifetime of the guarded container
        m = e.trips;
        if (e.scope !== undefined && e.scope < depth) m = e.trips;
      } else m = A.mul(m, e.trips);
    }
    void v;
    return m;
  }
  /** executions of the current position per invocation of the function (all loops) */
  multAll() { return this.multSince(0); }
  /** multiplier of the loops that surround the *declaration depth* d (used for per-lifetime scaling) */
  multUntil(d) {
    let m = ONE;
    const L = this.fr.loops;
    for (let i = 0; i < Math.min(d, L.length); i++) m = L[i].global ? L[i].trips : A.mul(m, L[i].trips);
    return m;
  }

  // ------------------------------------------------------------------ function lookup
  findFunc(name, cls = null) {
    const c = this.funcs.filter((f) => f.name === name);
    if (cls) { const x = c.find((f) => f.cls === cls); if (x) return x; }
    return c.find((f) => !f.isCtor) || c[0] || null;
  }
  fnKeyOf(f) { return `${f.cls ? f.cls + '.' : ''}${f.name}@${f.line}`; }

  resolveCall(e, env) {
    if (e.t !== 'call') return null;
    if (!e.recv) {
      const loc = env.def(e.fn);
      if (loc) return loc;
      if (/^[A-Za-z_]\w*$/.test(e.fn || '') || /^[A-Za-z_]\w*\.[A-Za-z_]\w*$/.test(e.fn || '')) {
        if (e.fn.includes('.')) { const [c, m] = e.fn.split('.'); const f = this.funcs.find((x) => x.cls === c && x.name === m); if (f) return f; return null; }
        const f = this.funcs.filter((x) => x.name === e.fn && !x.isCtor);
        if (f.length) return this.pickOverload(f, e.a.length, this.fr && this.fr.fn && this.fr.fn.cls);
      }
      return null;
    }
    const r = e.recv;
    if (r.t === 'id' && (r.n === 'self' || r.n === 'this' || r.n === 'Solution')) {
      const f = this.funcs.filter((x) => x.name === e.m && !x.isCtor);
      if (f.length) return this.pickOverload(f, e.a.length, this.fr && this.fr.fn && this.fr.fn.cls);
    }
    return null;
  }
  pickOverload(cands, n, cls) {
    const byN = cands.filter((f) => f.params.length === n);
    const pool = byN.length ? byN : cands;
    return pool.find((f) => f.cls === cls) || pool[0];
  }

  // ------------------------------------------------------------------ parameter records
  inferParamType(p, fn) {
    if (p.ty && p.ty.k !== 'unknown') return p.ty;
    // Python without a type hint: infer from how the parameter is used
    let seq = false, num = false, str = false, mapLike = false, tree = false, node = false;
    eachStmtExprs(fn.body, (e) => {
      if (e.t === 'call' && !e.recv && (e.fn === 'len') && e.a[0] && e.a[0].t === 'id' && e.a[0].n === p.n) seq = true;
      if (e.t === 'call' && !e.recv && e.fn === 'range') e.a.forEach((x) => { if (x.t === 'id' && x.n === p.n) num = true; });
      if (e.t === 'idx' && e.o.t === 'id' && e.o.n === p.n) seq = true;
      if (e.t === 'slice' && e.o.t === 'id' && e.o.n === p.n) seq = true;
      if (e.t === 'call' && e.recv && e.recv.t === 'id' && e.recv.n === p.n) { if (['append', 'extend', 'sort', 'pop', 'insert', 'reverse', 'index', 'count'].includes(e.m)) seq = true; if (['lower', 'upper', 'split', 'strip', 'isdigit', 'isalpha', 'startswith', 'endswith', 'join', 'replace', 'find'].includes(e.m)) str = true; if (['items', 'keys', 'values', 'get', 'setdefault'].includes(e.m)) mapLike = true; }
      if (e.t === 'attr' && e.o.t === 'id' && e.o.n === p.n) { if (e.n === 'left' || e.n === 'right') tree = true; if (e.n === 'next') node = true; }
      if (e.t === 'op' && ['+', '-', '*', '//', '%', '<', '>', '<=', '>=', '//'].includes(e.o) && e.a.some((x) => x.t === 'id' && x.n === p.n) && e.a.some((x) => x.t === 'num')) num = true;
    });
    for (const s of [fn.body]) eachStmt(s, (st) => { if (st.s === 'for' && st.mode === 'each' && st.iter.t === 'id' && st.iter.n === p.n) seq = true; if (st.s === 'for' && st.mode === 'range') [st.lo, st.hi].forEach((x) => { if (x && x.t === 'op' && x.a.some((y) => y.t === 'id' && y.n === p.n)) num = true; if (x && x.t === 'id' && x.n === p.n) num = true; }); });
    if (tree) return { k: 'tree', cls: 'TreeNode', inferred: true };
    if (node) return { k: 'node', cls: 'ListNode', inferred: true };
    if (mapLike) return { k: 'map', key: { k: 'unknown' }, e: { k: 'unknown' }, inferred: true };
    if (str) return { k: 'str', inferred: true };
    if (seq && !num) return { k: 'list', e: { k: 'unknown' }, impl: 'list', inferred: true };
    if (num && !seq) return { k: 'int', inferred: true };
    return { k: 'unknown' };
  }

  makeParams(fn, env, key) {
    for (const p of fn.params) {
      const ty = this.inferParamType(p, fn);
      env.set(p.n, { name: p.n, ty, isParam: true, ownerFn: key, depth: 0, ref: p.ref, inferred: ty.inferred });
      if (ty.inferred && ty.k !== 'unknown') this.assume(`\`${p.n}\` has no type hint; it is treated as ${ty.k === 'int' ? 'an integer' : ty.k === 'tree' ? 'a binary-tree node' : ty.k === 'node' ? 'a linked-list node' : ty.k === 'str' ? 'a string' : ty.k === 'map' ? 'a dictionary' : 'a list / sequence'} because of how the code uses it.`);
    }
  }

  // ------------------------------------------------------------------ entry point
  analyze(entryName) {
    const fn = this.findFunc(entryName);
    if (!fn) throw new Und(`the function \`${entryName}\` was not found in the code`);
    this.entry = fn;
    let result = null;
    let lastKey = null;
    for (let pass = 0; pass < 7; pass++) {
      this.paramSyms.length = 0;
      this.growthNow = new Map(); this.callsNow = new Map(); this.depthNow = new Map();
      this.recording = true;
      this.root = { kind: 'root', children: [], text: 'root' }; this.cur = this.root;
      this.calls = 0; this.spaceTerms = []; this.temps = [];
      this.stack = [];
      result = this.runEntry(fn);
      const key = this.passKey();
      this.growthPrev = this.growthNow; this.callsPrev = this.callsNow; this.depthPrev = this.depthNow;
      if (key === lastKey) { result.passes = pass + 1; return result; }
      lastKey = key;
    }
    throw new Und('the bound did not stabilise: the sizes of some containers depend on each other in a loop the analyzer cannot resolve', null, 'fixpoint');
  }
  passKey() {
    const parts = [];
    for (const [k, list] of this.growthNow) parts.push(k + '=' + list.map((g) => this.fmt(A.add(A.mul(g.mult, g.outer), A.mul(g.mult, g.total)))).join('|'));
    for (const [k, c] of this.callsNow) parts.push('c:' + k + '=' + this.fmt(c));
    for (const [k, c] of this.depthNow) parts.push('d:' + k + '=' + this.fmt(c));
    return parts.sort().join(';') + '#' + (this.lastResultKey || '');
  }

  runEntry(fn) {
    const key = this.fnKeyOf(fn);
    const env = new Env();
    this.registerDefs(fn, env);
    this.makeParams(fn, env, key);
    this.fr = { fn, fnKey: key, loops: [], global: [], depthCalls: 0, envRef: env };
    this.tagMarks(fn); this.tagBalanced(fn);
    this.callMult = ONE;
    this.stack.push(fn);
    this.curLine = fn.line;
    const top = this.node('func', fn.line, `\`${fn.name}\` — the function being analysed`);
    const out = this.within(top, () => this.analyzeBody(fn, env, key, true));
    this.stack.pop();
    this.lastResultKey = this.fmt(out.time) + '/' + (out.space.err ? 'err' : this.fmt(out.space.total));
    top && (top.cost = out.time);
    return { ...out, tree: this.root, fn };
  }

  registerDefs(fn, env) {
    for (const s of fn.body) if (s.s === 'def') env.defs.set(s.fn.name, { ...s.fn, nested: true, closure: env });
  }

  /** Analyse a function body (non-recursive or via the recursion templates). Returns {time, space}. */
  analyzeBody(fn, env, key, isEntry) {
    const rec = this.isRecursive(fn, key);
    if (rec) return this.analyzeRecursive(fn, env, key, rec, isEntry);
    const parts = this.runBody2(fn, env);
    this.fr.lifted = parts.lifted;
    const time = A.add(parts.per, parts.glob);
    const sp = this.spaceTotal(ONE, fn);
    if (!sp.err && this.fr.calleeErr) return { time, space: { err: this.fr.calleeErr } };
    return { time, space: sp };
  }

  runBody(fn, env) { const r = this.runBody2(fn, env); return A.add(r.per, r.glob); }
  runBody2(fn, env) {
    const per = this.block(fn.body, env);
    let glob = null; const lifted = [];
    for (const g of this.fr.global) { if (g.lift) lifted.push(g); else glob = glob ? A.add(glob, g.cost) : g.cost; }
    this.fr.global = [];
    return { per, glob: glob || ONE, hadGlobal: glob !== null || lifted.length > 0, lifted };
  }

  // ------------------------------------------------------------------ statements
  block(stmts, env) {
    let t = ONE;
    for (let i = 0; i < stmts.length; i++) {
      const s = stmts[i];
      if (s.mark && this.fr.fn) {
        const dom = this.tryDomain(s, env, stmts.slice(i + 1));
        if (dom) return A.add(t, this.region(s, dom, stmts.slice(i), env));
      }
      t = A.add(t, this.stmt(s, env));
    }
    return t;
  }
  pushGlobal(cost, line, text) {
    if (this.fr.liftRoot) this.fr.global.push({ cost, line, text, lift: true, root: this.fr.liftRoot });
    else this.fr.global.push({ cost, line, text });
  }
  tagBalanced(fn) {
    const POP = new Set(['pop_back', 'pop', 'removeLast', 'pop_front', 'popleft']);
    const PUSH = new Set(['push_back', 'append', 'add', 'push', 'addLast', 'emplace_back']);
    const walk = (list) => {
      list.forEach((s, i) => {
        if (s.s === 'expr' && s.e.t === 'call' && s.e.recv && s.e.recv.t === 'id' && PUSH.has(s.e.m)) {
          const nm = s.e.recv.n;
          for (let j = i + 1; j < list.length; j++) { const p = list[j]; if (p.s === 'expr' && p.e.t === 'call' && p.e.recv && p.e.recv.t === 'id' && p.e.recv.n === nm && POP.has(p.e.m) && p.e.a.length === 0) { s.e.bal = true; break; } if (p.s === 'break' || p.s === 'continue' || p.s === 'return') break; }
        }
        if (s.s === 'if') { walk(s.then); walk(s.else || []); } else if (s.s === 'while' || s.s === 'for') walk(s.body); else if (s.s === 'try') walk(s.body);
      });
    };
    walk(fn.body);
  }
  tryDomain(s, env, rest) {
    try { return this.markDomain(s, env, rest, s.line); } catch (err) { if (err instanceof Und) return null; throw err; }
  }
  /** the statements after a first-visit mark: executed at most once per distinct key */
  region(s, dom, rest, env) {
    const scale = this.multUntil(dom.V.depth || 0);
    const trips = A.mul(scale, dom.D);
    if (dom.assume) this.assume(dom.assume);
    const nd = this.node('region', s.line, `first-visit guard on \`${dom.V.name}\`: everything below runs once per distinct key`);
    if (nd) { nd.trips = trips; nd.why = dom.why; }
    const keep = this.fr.distinct; const keepReg = this.fr.regions; const keepLift = this.fr.liftRoot;
    { const rt = this.growthTarget(dom.V); if (rt.ownerFn !== this.fr.fnKey) this.fr.liftRoot = rt; }
    this.fr.distinct = new Set([...(keep || []), ...dom.keys]);
    this.fr.regions = [...(keepReg || []), { names: new Set(dom.keys) }];
    this.fr.usedRegion = trips;
    this.pushLoop(trips, { global: true });
    let c;
    try { c = this.within(nd, () => A.add(this.stmt(s, env), this.block(rest.slice(1), env))); } finally { this.popLoop(); this.fr.distinct = keep; this.fr.regions = keepReg; this.fr.liftRoot = keepLift; }
    const root = this.growthTarget(dom.V);
    if (root.ownerFn !== this.fr.fnKey) this.fr.global.push({ cost: A.mul(dom.D, c), line: s.line, text: 'guarded region', lift: true, root });
    else if (this.fr.liftRoot) this.fr.global.push({ cost: A.mul(trips, c), line: s.line, text: 'guarded region', lift: true, root: this.fr.liftRoot });
    else this.fr.global.push({ cost: A.mul(trips, c), line: s.line, text: 'guarded region' });
    if (nd) nd.cost = A.mul(trips, c);
    return ONE;
  }

  stmt(s, env) {
    this.curLine = s.line || this.curLine;
    const line = s.line || this.curLine;
    switch (s.s) {
      case 'decl': return this.declStmt(s, env);
      case 'assign': return this.assignStmt(s, env);
      case 'expr': {
        const c = this.ec(s.e, env);
        this.noteCost(s, c, `\`${show(s.e)}\``);
        return c;
      }
      case 'if': return this.ifStmt(s, env);
      case 'while': return this.whileStmt(s, env);
      case 'for': return this.forStmt(s, env);
      case 'return': { const c = s.v ? this.ec(s.v, env) : ONE; this.noteCost(s, c, `return ${show(s.v)}`); return c; }
      case 'break': case 'continue': case 'throw': return ONE;
      case 'switch': {
        let c = this.ec(s.disc, env); let worst = ONE;
        for (const b of s.cases) worst = A.add(worst, this.block(b, env));
        return A.add(c, worst);
      }
      case 'try': {
        let c = this.block(s.body, env);
        for (const h of s.handlers) c = A.add(c, this.block(h, env));
        return A.add(c, this.block(s.fin, env));
      }
      case 'del': { const t = s.target; let c = this.ec(t, env); if (t.t === 'idx' && this.typeOf(t.o, env).k === 'list') c = A.add(c, this.sizeOf(t.o, env, line)); return c; }
      case 'def': return ONE;
      default: return ONE;
    }
  }

  noteCost(s, c, text) {
    if (!this.recording || A.isOne(c)) return;
    const n = this.node('stmt', s.line, text, {});
    if (n) n.cost = c;
  }

  // -- declarations ---------------------------------------------------
  declStmt(s, env) {
    const line = s.line;
    let ty = s.ty && s.ty.k !== 'unknown' ? s.ty : (s.init ? this.typeOf(s.init, env) : { k: 'unknown' });
    if (s.init && s.init.t === 'new' && s.init.ty && s.init.ty.k !== 'unknown') ty = s.init.ty.k === 'array' && !(s.ty && s.ty.k === 'array') ? s.ty : (s.ty && s.ty.k !== 'unknown' ? s.ty : s.init.ty);
    let c = ONE;
    if (s.init) c = this.ec(s.init, env);
    // C++ value semantics: `vector<int> b = a;` copies, `vector<int>& b = a;` aliases
    const rec = { name: s.n, ty, isParam: false, ownerFn: this.fr.fnKey, depth: this.fr.loops.length, line, ref: s.ref };
    this.initVar(rec, s.init, env, line, true);
    env.set(s.n, rec);
    if (isContainer(ty) || ty.k === 'tree' || ty.k === 'node') this.noteLocalContainer(rec, line);
    return c;
  }

  /** fill in size / value information of a variable from its initialiser */
  initVar(rec, init, env, line, fresh) {
    const ty = rec.ty;
    if (!init) { if (isContainer(ty)) { rec.init = ONE; } return; }
    if (init.t === 'num') rec.cst = init.v;
    if (isContainer(ty)) {
      try { rec.init = this.sizeOf(init, env, line); } catch (err) { if (!(err instanceof Und)) throw err; rec.initErr = err.reason; }
      this.setInner(rec, init, env, line);
      // sharing: `a = b` in Java/Python (and C++ references) makes both names the same container
      if ((init.t === 'id' || init.t === 'idx' || init.t === 'attr') && (this.lang !== 'cpp' || rec.ref)) {
        const root = this.rootVar(init); const rv = root && env.get(root.n);
        if (rv) { rec.aliasOf = rv; if (rec.init === undefined && rv.init) rec.init = rv.init; }
      }
    } else if (ty.k === 'int' || ty.k === 'float' || ty.k === 'bool' || ty.k === 'unknown') {
      try { rec.val = this.mag(init, env, line); } catch (err) { if (!(err instanceof Und)) throw err; rec.noVal = err.reason; }
    }
    if ((ty.k === 'tree' || ty.k === 'node' || ty.k === 'nary') && init.t !== 'null') {
      const rt = this.treeRootOf(init, env);
      if (rt) rec.nodesOf = rt;
    }
    void fresh;
  }
  setInner(rec, init, env, line) {
    try {
      if (init.t === 'new' && init.a.length >= 2 && isContainer(this.typeOf(init.a[1], env)) || init.t === 'new' && init.a.length >= 2 && init.a[1].t === 'new') rec.inner = this.sizeOf(init.a[1], env, line);
      else if (init.t === 'new' && init.alloc && init.a.length >= 2) rec.inner = this.mag(init.a[1], env, line);
      else if (init.t === 'comp') { const inner = new Env(env); init.gens.forEach((g) => this.bindLoopVars(g.vars, g.iter, inner, ONE, line)); const et = this.typeOf(init.elt, inner); if (isContainer(et) || init.elt.t === 'lit' || init.elt.t === 'op' || init.elt.t === 'new') rec.inner = this.sizeOf(init.elt, inner, line); }
      else if (init.t === 'op' && init.o === '*') { const l = init.a[0]; if (l.t === 'lit' && l.a[0]) rec.inner = this.sizeOf(l.a[0], env, line); }
      else if (init.t === 'id') { const v = env.get(init.n); if (v && v.inner) rec.inner = v.inner; }
      else if (init.t === 'idx') { const r = this.rootVar(init.o); const v = r && env.get(r.n); if (v && v.inner2) rec.inner = v.inner2; }
    } catch (err) { if (!(err instanceof Und)) throw err; }
  }
  treeRootOf(e, env) {
    const r = this.rootVar(e); const v = r && env.get(r.n);
    return v ? (v.nodesOf || v) : null;
  }

  /** a local container is auxiliary space: remember it so the space analysis can sum the bounds at the end */
  noteLocalContainer(rec, line) {
    if (rec.aliasOf || rec.ref) return;
    (this.fr.locals = this.fr.locals || []).push({ rec, line });
  }

  // -- assignments ------------------------------------------------------
  assignStmt(s, env) {
    const line = s.line;
    const t = s.target;
    // tuple targets: a, b = b, a % b  /  l, r = 0, n - 1
    if (t.t === 'tuple') {
      let c = this.ec(s.v, env);
      const vals = s.v.t === 'lit' && s.v.kind === 'tuple' && s.v.a.length === t.a.length ? s.v.a : null;
      t.a.forEach((x, i) => { if (x.t === 'id') this.assignVar(x, '=', vals ? vals[i] : null, env, line, s.first); else if (x.t === 'idx' || x.t === 'attr') c = A.add(c, this.ec(x, env)); });
      return c;
    }
    const c = this.ec({ t: 'assign', op: s.op, target: t, v: s.v, line }, env);
    if (t.t === 'id') this.assignVar(t, s.op, s.v, env, line, s.first, s.ann);
    this.noteCost(s, c, `${show(t)} ${s.op} ${show(s.v)}`);
    return c;
  }
  /** x = value / x += value as seen from an expression (C++ / Java `assign` expression inside expression statements) */
  assignVar(t, op, v, env, line, first, ann) {
    let rec = env.get(t.n);
    if (!rec) {
      // Python: first assignment creates the variable
      const ty = ann && ann.k !== 'unknown' ? ann : (v ? this.typeOf(v, env) : { k: 'unknown' });
      rec = { name: t.n, ty, isParam: false, ownerFn: this.fr.fnKey, depth: this.fr.loops.length, line };
      if (v) this.initVar(rec, v, env, line, true);
      env.set(t.n, rec);
      if (isContainer(ty) || ty.k === 'tree' || ty.k === 'node') this.noteLocalContainer(rec, line);
      return;
    }
    this.reassign(rec, op, v, env, line);
  }
  reassign(rec, op, v, env, line) {
    if (!v) { rec.reassigned = true; return; }
    rec.reassigned = true; rec.cst = undefined;
    const ty = rec.ty;
    if (isContainer(ty)) {
      if (op === '=') {
        // a new container replaces the old one: its size bound is the max of the sizes it can have
        try { const sz = this.sizeOf(v, env, line); rec.init = rec.init ? A.add(rec.init, sz) : sz; } catch (err) { if (!(err instanceof Und)) throw err; rec.initErr = err.reason; rec.init = undefined; }
        if (!rec.inner) this.setInner(rec, v, env, line);
        if ((v.t === 'id' || v.t === 'idx') && this.lang !== 'cpp') { const root = this.rootVar(v); const rv = root && env.get(root.n); if (rv && !rec.isParam) rec.aliasOf = rv; }
        rec.totalInit = undefined;
      } else if (op === '+=' ) {
        try { this.recordGrowth(this.growthTarget(rec), this.sizeOf(v, env, line), this.sizeOf(v, env, line), line); } catch (err) { if (!(err instanceof Und)) throw err; throw new Und(`cannot bound how much \`${rec.name}\` grows in \`${rec.name} += ${show(v)}\``, line); }
      }
      return;
    }
    if (ty.k === 'int' || ty.k === 'float' || ty.k === 'bool' || ty.k === 'unknown') {
      if (rec.isParam && rec.val === undefined && !this.paramValUsed(rec)) { rec.pvals = (rec.pvals || []); }
      try {
        const m = this.mag(v, env, line);
        if (op === '=') rec.val = rec.val ? A.add(rec.val, m) : (rec.isParam ? undefined : m);
        else if (op === '+=' || op === '-=') { const w = A.mul(this.multSince(rec.ownerFn === this.fr.fnKey ? rec.depth || 0 : 0), m); rec.val = A.add(rec.val || (rec.isParam ? this.needVal(rec, line) : ONE), w); }
        else if (op === '*=' || op === '<<=') { if (v.t === 'num' && v.v === 1) return; rec.val = undefined; rec.noVal = `\`${rec.name}\` is multiplied repeatedly, so its value can grow exponentially`; }
        else if (op === '/=' || op === '//=' || op === '>>=' || op === '%=') { /* shrinks */ }
        else rec.val = A.add(rec.val || ONE, m);
      } catch (err) { if (!(err instanceof Und)) throw err; if (!rec.isParam) { rec.val = undefined; rec.noVal = err.reason; } else { rec.badAssign = err.reason; } }
    }
  }
  paramValUsed() { return false; }
  /** `a[i] = x` and `node.next = y`: no size change for arrays; a map insert counts as growth */
  noteElementWrite(t, v, env, line) {
    if (t.t === 'idx') {
      const rt = this.typeOf(t.o, env);
      if (rt.k === 'map' || rt.k === 'sortedmap') { const root = this.rootVar(t.o); const rec = root && env.get(root.n); if (rec) this.recordGrowth(this.growthTarget(rec), t.o.t === 'id' ? ONE : [], ONE, line); }
    }
  }
  growthTarget(rec) { let r = rec; while (r.aliasOf) r = r.aliasOf; return r; }

  // -- if -----------------------------------------------------------------
  ifStmt(s, env) {
    let c = this.ec(s.cond, env);
    const region = this.guardRegion(s, env);
    if (region) return A.add(c, region);
    const a = this.block(s.then, env);
    const b = s.else && s.else.length ? this.block(s.else, env) : ONE;
    return A.add(c, A.add(a, b));
  }
  guardRegion() { return null; }

  // ------------------------------------------------------------------ calls to user functions
  callUser(fn, e, env, line) {
    const key = this.fnKeyOf(fn);
    if (this.stack.some((f) => this.fnKeyOf(f) === key)) return this.recursiveCallSite(fn, e, env, line);
    if (++this.calls > MAX_CALLS) throw new Und('too many nested calls to analyse', line);
    const callee = new Env(fn.closure || null);
    this.registerDefs(fn, callee);
    this.bindArgs(fn, e, env, callee, line, key);
    const saved = { fr: this.fr, callMult: this.callMult };
    const myMult = A.mul(this.callMult, this.multSince(0));
    this.callsNow.set(key, this.callsNow.has(key) ? A.add(this.callsNow.get(key), myMult) : myMult);
    this.fr = { fn, fnKey: key, loops: [], global: [], parent: saved.fr, depthCalls: (saved.fr.depthCalls || 0) + 1, distinct: saved.fr.distinct && new Set(), envRef: callee };
    this.tagMarks(fn); this.tagBalanced(fn);
    this.callMult = myMult;
    this.stack.push(fn);
    const nd = this.node('call', line, `call to \`${fn.name}\``);
    let out;
    try { out = this.within(nd, () => this.analyzeBody(fn, callee, key, false)); } finally { this.stack.pop(); const calleeFr = this.fr; this.fr = saved.fr; this.callMult = saved.callMult; this.liftGlobals(calleeFr); }
    (this.fr.calleeSpace = this.fr.calleeSpace || []).push(out.space.err ? ONE : out.space.total); if (out.space.err) this.fr.calleeErr = out.space.err;
    if (nd) nd.cost = out.time;
    return out.time;
  }
  liftGlobals(calleeFr) {
    for (const t of calleeFr.lifted || []) {
      if (t.root.ownerFn === this.fr.fnKey) this.fr.global.push({ cost: A.mul(this.multUntil(t.root.depth || 0), t.cost), line: t.line, text: t.text });
      else this.fr.global.push({ ...t });
    }
  }

  /** bind each parameter to what we know about the argument expression */
  bindArgs(fn, e, env, callee, line, key) {
    fn.params.forEach((p, i) => {
      const a = e.a[i];
      let ty = p.ty && p.ty.k !== 'unknown' ? p.ty : (a ? this.typeOf(a, env) : { k: 'unknown' });
      if (ty.k === 'unknown' && a) ty = this.typeOf(a, env);
      const rec = { name: p.n, ty, isParam: false, ownerFn: key, depth: 0, ref: p.ref };
      if (a) {
        this.initVar(rec, a, env, line, true);
        if (isContainer(ty) && this.lang === 'cpp' && !p.ref && (a.t === 'id' || a.t === 'idx' || a.t === 'attr')) { /* by-value copy: cost charged at the call site */ rec.copied = true; }
        if (isContainer(ty) && (this.lang !== 'cpp' || p.ref)) { const root = this.rootVar(a); const rv = root && env.get(root.n); if (rv && (a.t === 'id')) { rec.aliasOf = this.growthTarget(rv); rec.init = rec.init === undefined ? rv.init : rec.init; rec.inner = rec.inner || rv.inner; } }
        if (ty.k === 'tree' || ty.k === 'node' || ty.k === 'nary') { const r = this.rootVar(a); const rv = r && env.get(r.n); if (rv) rec.nodesOf = rv.nodesOf || rv; }
      }
      callee.set(p.n, rec);
    });
  }
}

installCore(Analyzer);
installExprCost(Analyzer);
installLoops(Analyzer);
installRecursion(Analyzer);
installMarks(Analyzer);

// small shared predicates -------------------------------------------------------------------
export { Und };
