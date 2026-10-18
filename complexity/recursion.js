// Recursion analysis. A recursive function is analysed once to get its own per-call cost (recursive calls cost O(1) there);
// the number of calls is then derived by a template whose preconditions are verified on the code.
import * as A from './algebra.js';
import { Und, eachExpr, eachStmt, eachStmtExprs, eqE, idsIn, show } from './util.js';
import { isContainer } from './core.js';
import { num, conjuncts, cmpOf, assignedNames } from './loops.js';

const { ONE } = A;
const isId = (e, n) => e && e.t === 'id' && (n === undefined || e.n === n);
const TREE_FIELDS = new Set(['left', 'right', 'next', 'children', 'neighbors']);
const strip = (s) => s.replace(/^O\(|\)$/g, '');

export function installRecursion(C) {
  const P = C.prototype;

  // ------------------------------------------------------------------ detection
  P.isSiteOf = function (e, fn) {
    if (e.t !== 'call') return false;
    if (!e.recv) return e.fn === fn.name && (!fn.cls || true);
    return e.recv.t === 'id' && (e.recv.n === 'self' || e.recv.n === 'this') && e.m === fn.name;
  };
  P.isRecursive = function (fn) {
    let r = false;
    eachStmtExprs(fn.body, (e) => { if (this.isSiteOf(e, fn)) r = true; });
    // nested helper defined inside and calling itself
    eachStmt(fn.body, (s) => { if (s.s === 'def') void s; });
    return r ? { fn } : null;
  };
  P.recursiveCallSite = function (fn, e, env, line) {
    if (!this.fr.rec || this.fnKeyOf(this.fr.fn) !== this.fnKeyOf(fn)) throw new Und(`\`${fn.name}\` is part of a mutual / indirect recursion, which the analyzer does not model`, line, 'recursion');
    const mult = this.multSince(0);
    (this.fr.rec.siteMults = this.fr.rec.siteMults || []).push({ mult, inRegion: this.fr.loops.some((l) => l.global), line });
    return ONE;
  };

  /** the sites of a recursive function (from the IR) and the most calls one invocation can make */
  P.siteInfo = function (fn) {
    const sites = [];
    const countE = (e, loop, conds) => {
      const cnt = (x) => {
        if (!x || typeof x !== 'object') return 0;
        if (x.t === 'op' && x.o === '?:') return cnt(x.a[0]) + Math.max(cnt(x.a[1]), cnt(x.a[2]));
        let n = 0;
        if (this.isSiteOf(x, fn)) { n++; sites.push({ e: x, loop, conds }); }
        const kids = [];
        switch (x.t) {
          case 'op': case 'lit': case 'tuple': kids.push(...x.a); break;
          case 'call': if (x.recv) kids.push(x.recv); kids.push(...x.a); break;
          case 'idx': kids.push(x.o, x.i); break;
          case 'slice': kids.push(x.o, x.lo, x.hi, x.step); break;
          case 'attr': kids.push(x.o); break;
          case 'new': kids.push(...x.a); if (x.init) kids.push(x.init); break;
          case 'assign': kids.push(x.target, x.v); break;
          case 'incdec': kids.push(x.target); break;
          default: break;
        }
        for (const k of kids) n += cnt(k);
        return n;
      };
      return cnt(e);
    };
    const go = (stmts, loop, conds) => {
      let n = 0;
      for (const s of stmts) {
        switch (s.s) {
          case 'if': { n += countE(s.cond, loop, conds); n += Math.max(go(s.then, loop, [...conds, s.cond]), go(s.else || [], loop, [...conds, { t: 'op', o: '!', a: [s.cond] }])); break; }
          case 'while': n += countE(s.cond, true, conds) + go(s.body, true, conds); break;
          case 'for': { let c = 0; for (const x of [s.iter, s.lo, s.hi, s.step, s.cond]) if (x) c += countE(x, loop, conds); const b = go([...(s.init || []), ...s.body, ...(s.update || [])], true, conds); n += c + b; s.__sites = b; break; }
          case 'switch': { n += countE(s.disc, loop, conds); let m = 0; for (const b of s.cases) m = Math.max(m, go(b, loop, conds)); n += m; break; }
          case 'try': n += go(s.body, loop, conds) + s.handlers.reduce((m, h) => Math.max(m, go(h, loop, conds)), 0) + go(s.fin, loop, conds); break;
          case 'decl': if (s.init) n += countE(s.init, loop, conds); break;
          case 'assign': n += countE(s.v, loop, conds); break;
          case 'expr': n += countE(s.e, loop, conds); break;
          case 'return': if (s.v) n += countE(s.v, loop, conds); break;
          default: break;
        }
      }
      return n;
    };
    const k = go(fn.body, false, []);
    return { k, sites, inLoop: sites.some((x) => x.loop) };
  };

  // ------------------------------------------------------------------ main entry
  P.analyzeRecursive = function (fn, env, key, rec, isEntry) {
    const info = this.siteInfo(fn);
    this.fr.rec = { key, fn, info };
    const nd = this.node('recursion', fn.line, `\`${fn.name}\` calls itself — up to ${info.k} recursive call${info.k === 1 ? '' : 's'} per invocation`);
    return this.within(nd, () => {
      const parts = this.runBody2(fn, env);
      this.fr.rec.parts = parts;
      const own = A.add(parts.per, parts.glob);
      if (!parts.lifted.length) this.fr.lifted = [];
      const locals = this.fr.locals || [];
      const plan = this.recursionPlan(fn, env, info, own, isEntry);
      if (nd) { nd.own = own; nd.plan = plan; nd.cost = plan.time; }
      this.fr.lifted = plan.lifted || parts.lifted;
      if (parts.lifted.length && plan.kind !== 'visited-recursion') throw new Und('a visited-set shared with the caller is used, but the recursion pattern around it was not recognised', fn.line, 'recursion');
      if (plan.calls) this.callsNow.set(key, A.mul(this.callMult || ONE, plan.calls));
      if (plan.depth) this.depthNow.set(key, plan.depth);
      let space;
      try {
        const frame = this.frameSpace(locals);
        let total = plan.depth ? A.mul(plan.depth, frame) : frame; let geo = false;
        if (plan.kind === 'divide-and-conquer' && plan.master) { const syms = [...A.symbolsIn(plan.master.f)]; if (syms.length === 1 && A.degreeIn(frame, syms[0]) >= 1) { total = frame; geo = true; } }
        space = { total, depth: plan.depth, frame, rec: true, depthWhy: plan.depthWhy, geometric: geo };
      } catch (err) { if (!(err instanceof Und)) throw err; space = { err }; }
      return { time: plan.time, space };
    });
  };

  P.frameSpace = function (locals) {
    let t = ONE;
    const outs = this.returnedNames(this.fr.fn);
    for (const { rec } of locals) { if (outs.has(rec.name)) continue; if (rec.initErr) throw new Und(`cannot bound the size of local \`${rec.name}\`: ${rec.initErr}`, rec.line); if (rec.init) t = A.add(t, this.totalBound(rec)); }
    for (const tm of this.fr.temps || []) t = A.add(t, tm.size);
    return t;
  };

  // ------------------------------------------------------------------ templates
  P.recursionPlan = function (fn, env, info, own, isEntry) {
    void isEntry;
    const line = fn.line;
    if (info.k === 0) throw new Und('no recursive call found', line);
    const memo = this.memoKind(fn, env);
    const sub = this.subsetLoopPlan(fn, env, info, own);
    if (sub) return sub;
    const tree = this.treePlan(fn, env, info, own);
    if (tree) return tree;
    const span = this.spanHalvingPlan(fn, env, info, own);
    if (span) return span;
    const graph = this.visitedPlan(fn, env, info, own);
    if (graph) return graph;
    if (info.inLoop && !memo) throw new Und('a recursive call inside a loop — the number of calls depends on how many iterations take the recursive path, and no counting template (subsets by index / memoisation) applies', line, 'recursion');
    const params = this.measureParams(fn, env, info, line);
    if (memo) return this.memoPlan(fn, env, info, own, params, memo);
    return this.measurePlan(fn, env, info, own, params);
  };

  /** classify how every parameter changes over all recursive call sites */
  P.measureParams = function (fn, env, info, line) {
    const out = [];
    fn.params.forEach((p, i) => {
      const forms = info.sites.map((s) => this.argForm(s.e.a[i], p, fn, env));
      const kinds = new Set(forms.map((f) => f.kind));
      let kind = 'other';
      if (kinds.size === 1) kind = [...kinds][0];
      else if (forms.every((f) => f.kind === 'dec' || f.kind === 'same')) kind = 'dec-mixed';
      out.push({ p, i, forms, kind });
    });
    void line;
    return out;
  };
  P.argForm = function (a, p, fn, env) {
    if (!a) return { kind: 'other' };
    if (isId(a, p.n)) return { kind: 'same' };
    if (a.t === 'op' && a.o === '-' && isId(a.a[0], p.n)) { const c = num(a.a[1]); return c !== null && c >= 1 ? { kind: 'dec', c } : { kind: 'dec', c: 1, varStep: a.a[1] }; }
    if (a.t === 'op' && a.o === '+' && isId(a.a[0], p.n)) { const c = num(a.a[1]); return c !== null && c >= 1 ? { kind: 'inc', c } : { kind: 'other' }; }
    if (a.t === 'incdec' && isId(a.target, p.n)) return a.op === '--' ? { kind: 'dec', c: 1 } : { kind: 'inc', c: 1 };
    if (a.t === 'op' && (a.o === '/' || a.o === '//') && isId(a.a[0], p.n) && num(a.a[1]) >= 2) return { kind: 'half', c: num(a.a[1]) };
    if (a.t === 'op' && a.o === '>>' && isId(a.a[0], p.n) && num(a.a[1]) >= 1) return { kind: 'half', c: 2 ** num(a.a[1]) };
    if (a.t === 'op' && a.o === '/' && false) return { kind: 'other' };
    void fn; void env;
    return { kind: 'other', e: a };
  };

  /** a test in an early-exit `if` that bounds parameter p: returns {lo|hi: bound expr} */
  P.baseBounds = function (fn, p, info) {
    const res = { lower: false, upper: null };
    const firstSite = (stmt) => { let r = false; eachStmtExprs([stmt], (e) => { if (this.isSiteOf(e, fn)) r = true; }); return r; };
    const exits = (list) => list.length && list.every((s) => s.s === 'return' || s.s === 'throw' || (s.s === 'if' && exits(s.then) && s.else && exits(s.else)) ) || (list.length && ['return', 'throw'].includes(list[list.length - 1].s));
    for (const s of fn.body) {
      if (s.s === 'if' && exits(s.then) && !firstSite(s)) {
        for (const d of conjuncts(s.cond, '||')) {
          const parts = conjuncts(d, '&&');
          for (const c of parts) {
            const cm = cmpOf(c, p.n);
            if (!cm) continue;
            if (['<', '<=', '=='].includes(cm.op) && num(cm.bound) !== null) res.lower = true;
            if (['>=', '>', '=='].includes(cm.op)) res.upper = res.upper || cm.bound;
            if (cm.op === '==') res.upper = res.upper || cm.bound;
          }
        }
        if (s.cond.t === 'op' && s.cond.o === 'in' && isId(s.cond.a[0], p.n)) res.lower = true;
      }
      if (firstSite(s)) break;
    }
    // sites guarded by an enclosing `if` on p
    for (const st of info.sites) for (const c of st.conds) for (const x of conjuncts(c)) { const cm = cmpOf(x, p.n); if (cm) { if (['>', '>=', '!='].includes(cm.op) && num(cm.bound) !== null) res.lower = true; if (['<', '<='].includes(cm.op)) res.upper = res.upper || cm.bound; } }
    return res;
  };

  // -- tree / linked-list recursion ---------------------------------------------------------
  P.treePlan = function (fn, env, info, own) {
    if (info.inLoop && !info.sites.every((s) => s.e.a.some((a) => a.t === 'idx' || a.t === 'attr' || a.t === 'id'))) return null;
    // the first argument (or one argument) of every site must be a child of a tree/list parameter
    for (let i = 0; i < fn.params.length; i++) {
      const p = fn.params[i];
      const rec = env.get(p.n);
      if (!rec || !['tree', 'node', 'nary'].includes(rec.ty.k)) continue;
      const fields = new Set();
      const ok = info.sites.every((s) => { const a = s.e.a[i]; if (!a) return false; let x = a; while (x.t === 'attr' && TREE_FIELDS.has(x.n)) { fields.add(x.n); x = x.o; } if (isId(x, p.n) && x !== a) return true; if (a.t === 'idx' && a.o.t === 'attr' && TREE_FIELDS.has(a.o.n) && isId(a.o.o, p.n)) { fields.add(a.o.n); return true; } if (s.loop && isId(a)) { fields.add('children'); return true; } return false; });
      if (!ok) continue;
      // other parameters must not grow between calls (their sizes feed the per-call cost)
      this.requireStable(fn, env, info, i, own);
      const root = rec.nodesOf || rec;
      const isTree = fields.has('left') || fields.has('right') || fields.has('children');
      const N = this.nodeSym(root, 'nodes', fn.line);
      const H = isTree ? this.nodeSym(root, 'height', fn.line) : N;
      const time = A.mul(N, own);
      const depth = H;
      return { kind: 'structural', time, depth, calls: N, why: `the recursion moves from \`${p.n}\` to one of its children (${[...fields].map((f) => '.' + f).join(', ')}) and never comes back, so every node of the ${isTree ? 'tree' : 'list'} is the argument of at most ${info.k} call${info.k === 1 ? '' : 's'} (plus the calls on empty children): ≤ ${strip(this.fmt(N))} · ${info.k + 1} calls in total`, base: `a call on an empty node returns immediately`, depthWhy: isTree ? `the recursion is as deep as the tree is tall (h, between log n and n)` : `the recursion goes down the whole list: depth n` };
    }
    return null;
  };
  P.nodeSym = function (root, what, line) {
    if (!root.isParam && !root.nodesCount) throw new Und(`cannot tell how many nodes \`${root.name}\` has (it is not an input parameter)`, line);
    if (root.nodesCount) return what === 'height' ? root.heightSym : root.nodesCount;
    if (what === 'height') return this.pSym(`h:${root.name}`, 'h', `height of the tree \`${root.name}\``, 'h', 'height', root.name);
    return this.pSym(`nodes:${root.name}`, 'n', `number of nodes of \`${root.name}\``, 'n', 'nodes', root.name);
  };
  /** the cost of one call must not depend on parameters that change from call to call (other than the measure) */
  P.requireStable = function (fn, env, info, measureIdx, own) {
    const used = A.symbolsIn(own);
    fn.params.forEach((p, i) => {
      if (i === measureIdx) return;
      const rec = env.get(p.n);
      if (!rec) return;
      const syms = [rec.size, rec.val, rec.init, rec.inner].filter(Boolean).flatMap((e) => (Array.isArray(e) ? [...A.symbolsIn(e)] : []));
      const mentioned = syms.some((s) => used.has(s));
      if (!mentioned) return;
      const stable = info.sites.every((s) => { const a = s.e.a[i]; return a && (isId(a, p.n) || (a.t === 'op' && ['-', '//', '/'].includes(a.o) && isId(a.a[0], p.n) && num(a.a[1]) !== null)); });
      if (!stable) throw new Und(`the cost of one call depends on parameter \`${p.n}\`, and the recursive calls pass a different \`${p.n}\` — its size at deeper levels cannot be bounded by the rules`, fn.line, 'recursion');
    });
  };

  // -- measure on an int parameter -----------------------------------------------------------
  P.measurePlan = function (fn, env, info, own, params) {
    const line = fn.line;
    const cand = params.find((q) => (q.kind === 'dec' || q.kind === 'dec-mixed' || q.kind === 'inc' || q.kind === 'half') && q.forms.some((f) => f.kind !== 'same'));
    if (!cand) throw new Und('no parameter strictly decreases (or counts toward a bound) in every recursive call, so the depth of the recursion cannot be bounded', line, 'recursion');
    const rec = env.get(cand.p.n);
    const b = this.baseBounds(fn, cand.p, info);
    const k = info.k;
    this.requireStable(fn, env, info, cand.i, own);
    if (cand.kind === 'dec' || cand.kind === 'dec-mixed') {
      if (!b.lower) throw new Und(`no base case that stops the recursion when \`${cand.p.n}\` gets small was found (e.g. \`if ${cand.p.n} <= 0: return\`)`, line, 'recursion');
      if (cand.forms.some((f) => f.kind === 'same')) throw new Und(`\`${cand.p.n}\` does not shrink in some recursive calls`, line, 'recursion');
      const mu = this.measureMag(rec, cand.p, line, env);
      const cmin = Math.min(...cand.forms.map((f) => f.c));
      if (cand.forms.some((f) => f.varStep)) this.assume(`The amount subtracted from \`${cand.p.n}\` in each recursive call is at least 1 (otherwise the recursion would never end).`);
      return this.countCalls(fn, k, mu, cmin, own, `\`${cand.p.n}\` goes down by ${cmin}${cand.forms.some((f) => f.c !== cmin) ? '+' : ''} on every recursive call and the recursion stops once it gets to the base case`, A.add(mu, ONE), line);
    }
    if (cand.kind === 'inc') {
      if (!b.upper) throw new Und(`no base case compares \`${cand.p.n}\` with an upper limit (e.g. \`if ${cand.p.n} == n: return\`), so the number of levels cannot be bounded`, line, 'recursion');
      const mu = A.add(this.mag(b.upper, env, line), this.measureMag(rec, cand.p, line, env));
      const cmin = Math.min(...cand.forms.map((f) => f.c));
      return this.countCalls(fn, k, mu, cmin, own, `\`${cand.p.n}\` goes up by ${cmin}${cand.forms.some((f) => f.c !== cmin) ? '+' : ''} on every call and the base case stops it at \`${show(b.upper)}\` (≈ ${strip(this.fmt(mu))} levels)`, A.add(mu, ONE), line);
    }
    // half
    if (!b.lower) throw new Und(`no base case that stops the recursion when \`${cand.p.n}\` becomes small was found`, line, 'recursion');
    const mu = this.measureMag(rec, cand.p, line, env);
    return this.masterPlan(fn, k, mu, Math.min(...cand.forms.map((f) => f.c)), own, `\`${cand.p.n}\` is divided by ${Math.min(...cand.forms.map((f) => f.c))} on every call`, line);
  };
  P.measureMag = function (rec, p, line, env) {
    if (isContainer(rec.ty)) return this.sizeOf({ t: 'id', n: p.n }, env, line);
    return this.initMag(rec, line);
  };

  /** k calls per level, the measure shrinks by `step` each level */
  P.countCalls = function (fn, k, mu, step, own, why, depth, line) {
    if (k === 1) {
      return { kind: 'linear-recursion', time: A.mul(A.add(mu, ONE), own), depth, calls: A.add(mu, ONE), why: `${why}: at most ${strip(this.fmt(A.add(mu, ONE)))} nested calls in a chain, one call per level`, depthWhy: `depth = ${strip(this.fmt(depth))} (one frame per level)` };
    }
    const m = mu.length === 1 && !mu[0].x && !mu[0].f ? mu[0] : null;
    const syms = m ? Object.keys(m.p) : [];
    if (!m || syms.length !== 1 || m.p[syms[0]] !== 1 || Object.keys(m.l).length) throw new Und(`the recursion has ${k} calls per level but its depth ${this.fmt(mu)} is not a single linear symbol, so the size of the call tree cannot be stated`, line, 'recursion');
    const base = step === 1 ? k : Math.pow(k, 1 / step);
    const calls = A.expE(base, mu);
    this.assume(`The recursion tree is bounded by ${k}^depth; the real count can be smaller (an upper bound, e.g. Fibonacci really grows like 1.618ⁿ).`);
    return { kind: 'branching-recursion', time: A.mul(calls, own), depth, calls, upper: true, why: `${why}; each call makes up to ${k} further calls, so the call tree has at most ${k}^(${strip(this.fmt(mu))}${step > 1 ? ' / ' + step : ''}) nodes (upper bound)`, depthWhy: `depth = ${strip(this.fmt(depth))}` };
  };

  /** T(n) = a·T(n/b) + f(n) with f = own */
  P.masterPlan = function (fn, a, mu, b, own, why, line) {
    const m = mu.length === 1 && !mu[0].x && !mu[0].f ? mu[0] : null;
    const syms = m ? Object.keys(m.p) : [];
    if (!m || syms.length !== 1 || m.p[syms[0]] !== 1) throw new Und(`the size measure ${this.fmt(mu)} is not a single symbol, so the Master theorem cannot be applied`, line, 'recursion');
    const s = syms[0];
    const c = A.degreeIn(own, s); const lg = own.reduce((x, t) => Math.max(x, t.l[s] || 0), 0);
    const others = [...A.symbolsIn(own)].filter((x) => x !== s);
    if (others.length) throw new Und(`the per-call cost ${this.fmt(own)} depends on more than the measure \`${this.symName(s)}\``, line, 'recursion');
    const crit = Math.log(a) / Math.log(b);
    const S = A.sym(s);
    let time, case_;
    if (Math.abs(crit - Math.round(crit)) > 1e-9) throw new Und(`T(n) = ${a}·T(n/${b}) + ${this.fmt(own)}: the exponent log_${b}(${a}) is not an integer`, line, 'recursion');
    const ce = Math.round(crit);
    if (c < ce) { time = A.pow(S, ce); case_ = `f(n) = ${this.fmt(own)} grows slower than n^${ce}: the ${ce === 0 ? 'depth (log n)' : 'leaves'} dominate`; if (ce === 0) time = A.mul(A.add(A.logE(S), ONE), own); }
    else if (c === ce) { time = A.mul(A.add(A.logE(S), ONE), own); case_ = `f(n) = ${this.fmt(own)} grows as fast as n^${ce}: every one of the log n levels costs the same, so multiply by log n`; if (lg > 0) throw new Und('extra log factors in the per-call cost (Master theorem case 2 with polylog)', line, 'recursion'); }
    else { time = own; case_ = `f(n) = ${this.fmt(own)} grows faster than n^${ce}: the top level dominates (geometric series)`; }
    return { kind: 'divide-and-conquer', time, depth: A.add(A.logE(S), ONE), calls: null, why: `${why}; ${a} call${a === 1 ? '' : 's'} per level on a problem ${b} times smaller → T(n) = ${a}·T(n/${b}) + ${this.fmt(own)}. Master theorem: ${case_}`, master: { a, b, f: own }, depthWhy: `depth = log₂ n (the problem halves each level)` };
  };

  // -- visited-guarded recursion (graph / grid DFS) ---------------------------------------------
  P.visitedPlan = function (fn, env, info) {
    const rc = this.fr.rec; const parts = rc.parts;
    if (!parts.hadGlobal || !rc.siteMults || !rc.siteMults.length) return null;
    if (!rc.siteMults.every((s) => s.inRegion)) return null;
    if (!this.fr.usedRegion) return null;
    let calls = ONE;
    for (const s of rc.siteMults) calls = A.add(calls, s.mult);
    // every call costs its own prefix (guard tests); the guarded regions are paid once per distinct key
    let time = A.add(A.mul(calls, parts.per), parts.glob);
    let lifted = null;
    if (parts.lifted.length) {
      // the guard is shared with the caller: all calls together do the guarded work once per key, charged to the caller
      let extra = ONE; for (const s of rc.siteMults) extra = A.add(extra, s.mult);
      lifted = [...parts.lifted, { cost: A.mul(extra, parts.per), root: parts.lifted[0].root, line: fn.line, text: 'recursive calls' }];
      time = A.add(parts.per, parts.glob);
    }
    void info;
    const depth = this.fr.usedRegion;
    return { kind: 'visited-recursion', time, depth, calls, lifted, why: `a call only does real work the first time it sees a key (a first-visit mark protects everything after it), so the work below the mark happens at most ${strip(this.fmt(this.fr.usedRegion))} times in total; every recursive call is made from inside that guarded part, so the total number of calls is ≤ 1 + ${strip(this.fmt(calls))}`, depthWhy: `a chain of calls never revisits a key, so depth ≤ ${strip(this.fmt(depth))}` };
  };

  // -- merge-sort style: sites (lo, mid) and (mid+1, hi) with mid = midpoint ------------------
  P.spanHalvingPlan = function (fn, env, info, own) {
    const line = fn.line;
    // (1) index form: f(l, mid), f(mid + 1, r) with mid = (l + r) / 2
    if (fn.params.length >= 2 && info.k === 2 && info.sites.length === 2 && !info.inLoop) {
      for (let i = 0; i < fn.params.length; i++) for (let j = 0; j < fn.params.length; j++) {
        if (i === j) continue;
        const L = fn.params[i].n, R = fn.params[j].n;
        let mid = null;
        eachStmt(fn.body, (s) => { const t = s.s === 'decl' ? s.n : s.s === 'assign' && s.target.t === 'id' ? s.target.n : null; const v = s.s === 'decl' ? s.init : s.s === 'assign' ? s.v : null; if (t && v && this.isMidpoint(v, L, R)) mid = t; });
        if (!mid) continue;
        const a = info.sites.map((x) => [x.e.a[i], x.e.a[j]]);
        const left = a.find(([x, y]) => isId(x, L) && isId(y, mid));
        const right = a.find(([x, y]) => this.offsetOf(x, mid) === 1 && isId(y, R));
        const left2 = a.find(([x, y]) => isId(x, L) && this.offsetOf(y, mid) === -1);
        const right2 = a.find(([x, y]) => isId(x, mid) && isId(y, R));
        const ok = (left && right) || (left2 && right2);
        if (!ok) continue;
        const b = this.baseBounds(fn, fn.params[i], info);
        void b;
        // the base case must test `l >= r` / `l == r` / `r - l <= 1`
        if (!this.hasIntervalBase(fn, L, R)) continue;
        const span = A.add(this.mag({ t: 'id', n: R }, env, line), this.mag({ t: 'id', n: L }, env, line));
        const own2 = own;
        this.requireStableMany(fn, env, info, [i, j], own2);
        // the cost of one call is a function of (l, r): express it by the span = r - l
        const spanSym = this.spanSymbol(span, own, env, fn, [L, R], line);
        const res = this.masterPlan(fn, 2, spanSym.mu, 2, spanSym.own, `the interval [${L}, ${R}] is split at its midpoint \`${mid}\` into two halves`, line);
        res.depth = A.add(A.logE(spanSym.mu), ONE);
        return res;
      }
    }
    // (2) slice form: f(a[:mid]) and f(a[mid:]) with mid = len(a) // 2
    if (info.k === 2 && info.sites.length === 2 && !info.inLoop) {
      for (let i = 0; i < fn.params.length; i++) {
        const p = fn.params[i];
        let midName = null;
        eachStmt(fn.body, (s) => { const t = s.s === 'decl' ? s.n : s.s === 'assign' && s.target.t === 'id' ? s.target.n : null; const v = s.s === 'decl' ? s.init : s.s === 'assign' ? s.v : null; if (t && v && v.t === 'op' && (v.o === '//' || v.o === '/') && num(v.a[1]) === 2 && ((v.a[0].t === 'call' && v.a[0].fn === 'len' && isId(v.a[0].a[0], p.n)) || (v.a[0].t === 'call' && v.a[0].recv && isId(v.a[0].recv, p.n) && ['size', 'length'].includes(v.a[0].m)))) midName = t; });
        if (!midName) continue;
        const forms = info.sites.map((x) => x.e.a[i]);
        const isSl = (x, lo, hi) => x && x.t === 'slice' && isId(x.o, p.n) && ((lo && x.lo && isId(x.lo, midName) && !x.hi) || (hi && x.hi && isId(x.hi, midName) && !x.lo));
        if (!(forms.some((x) => isSl(x, false, true)) && forms.some((x) => isSl(x, true, false)))) continue;
        const rec = env.get(p.n);
        const mu = this.sizeOf({ t: 'id', n: p.n }, env, line);
        this.requireStable(fn, env, info, i, own);
        return this.masterPlan(fn, 2, mu, 2, own, `\`${p.n}\` is cut at its middle \`${midName} = len(${p.n}) // 2\` into two halves (slices)`, line) || (rec, null);
      }
    }
    return null;
  };
  P.hasIntervalBase = function (fn, L, R) {
    for (const s of fn.body) {
      if (s.s !== 'if') continue;
      for (const d of conjuncts(s.cond, '||')) { const m = d.t === 'op' && ['>=', '==', '>', '<=', '<'].includes(d.o) ? d : null; if (m) { const ids = idsIn(m); if (ids.has(L) && ids.has(R)) return true; } }
    }
    // body wrapped in `if l < r:`
    return fn.body.some((s) => s.s === 'if' && conjuncts(s.cond).some((c) => c.t === 'op' && ['<', '<=', '>', '>=', '!='].includes(c.o) && idsIn(c).has(L) && idsIn(c).has(R)));
  };
  P.requireStableMany = function () { /* handled through spanSymbol */ };
  /** replace the per-call cost's symbols of (l, r) by one span symbol */
  P.spanSymbol = function (span, own, env, fn, names, line) {
    const sv = names.map((n) => { const r = env.get(n); return r && r.val ? r.val : null; });
    // l is usually 0 at the top, so the span is just the magnitude of r + l
    const symsSpan = [...A.symbolsIn(span)];
    if (symsSpan.length !== 1) {
      throw new Und(`the interval bounds ${names.join(', ')} are not a single size, so the interval size cannot be tracked (they are ${this.fmt(span)})`, line, 'recursion');
    }
    void sv; void fn;
    const mu = span;
    const syms = [...A.symbolsIn(own)];
    if (syms.some((x) => !symsSpan.includes(x))) throw new Und(`the per-call cost ${this.fmt(own)} depends on more than the interval size`, line, 'recursion');
    return { mu, own };
  };

  // -- subsets by index inside a loop: for i in range(start, n): dfs(i + 1) ---------------------
  P.subsetLoopPlan = function (fn, env, info, own) {
    if (!info.inLoop || info.k < 1) return null;
    const line = fn.line;
    // find a `for` whose range starts at a parameter and whose recursive call passes `i + 1` for that parameter
    let found = null;
    eachStmt(fn.body, (s) => {
      if (found || s.s !== 'for') return;
      const loopVar = (s.vars && s.vars[0]) || null;
      let startE = null, endE = null;
      if (s.mode === 'range' && s.lo && s.lo.t === 'id') { startE = s.lo; endE = s.hi; }
      else if (s.mode === 'c' && s.init.length === 1 && s.init[0].s === 'decl' && s.init[0].init && s.init[0].init.t === 'id') { startE = s.init[0].init; const cm = cmpOf(s.cond, s.init[0].n); if (cm && ['<', '<='].includes(cm.op)) endE = cm.bound; }
      const lv = s.mode === 'c' ? s.init[0].n : loopVar;
      if (!startE || !endE || !lv) return;
      const idx = fn.params.findIndex((p) => p.n === startE.n);
      if (idx < 0) return;
      const sitesIn = [];
      eachStmtExprs(s.body, (e) => { if (this.isSiteOf(e, fn)) sitesIn.push(e); });
      if (!sitesIn.length || sitesIn.length !== info.sites.length) return;
      if (!sitesIn.every((e) => e.a[idx] && e.a[idx].t === 'op' && e.a[idx].o === '+' && isId(e.a[idx].a[0], lv) && num(e.a[idx].a[1]) >= 1)) return;
      // the loop var and the end must not change inside, and the loop must not be nested in another loop
      if (assignedNames(s.body).has(lv) && s.mode !== 'c') return;
      found = { s, idx, endE, startName: startE.n };
    });
    if (!found) return null;
    this.requireStable(fn, env, info, found.idx, own);
    const n = this.mag(found.endE, env, line);
    const rec = env.get(fn.params[found.idx].n);
    const mu = A.add(n, this.initMag(rec, line));
    const m = mu.length === 1 ? Object.keys(mu[0].p) : [];
    if (m.length !== 1) throw new Und(`the loop bound ${this.fmt(mu)} is not a single symbol`, line, 'recursion');
    const calls = A.expE(2, A.sym(m[0]));
    return { kind: 'subsets', time: A.mul(calls, own), depth: A.add(mu, ONE), calls, upper: true, why: `each call picks the next element from \`${found.startName}\` onward and recurses with \`i + 1\`: every call corresponds to a different increasing choice of indices, so there are at most 2^(${strip(this.fmt(mu))}) calls (one per subset)`, depthWhy: `depth ≤ ${strip(this.fmt(mu))} (the start index grows by at least 1 per level)` };
  };

  // -- memoisation ------------------------------------------------------------------------------
  P.memoKind = function (fn, env) {
    if ((fn.decorators || []).some((d) => /^(lru_cache|cache)$/.test(d))) return { kind: 'decorator', text: '`@lru_cache` / `@cache` stores the result of every distinct argument tuple' };
    const pnames = new Set(fn.params.map((p) => p.n));
    const local = new Set(); eachStmt(fn.body, (s) => { if (s.s === 'decl') local.add(s.n); if (s.s === 'assign' && s.target.t === 'id') local.add(s.target.n); });
    for (const s of fn.body) {
      if (s.s !== 'if' || !s.then.length) continue;
      const last = s.then[s.then.length - 1];
      if (last.s !== 'return' || !last.v) continue;
      const names = [...idsIn(s.cond)].filter((n) => !pnames.has(n) && !local.has(n));
      for (const n of names) {
        // the memo container is written inside the function
        let written = false;
        eachStmt(fn.body, (x) => { if (x.s === 'assign' && x.target.t === 'idx' && isId(x.target.o, n)) written = true; if (x.s === 'expr' && x.e.t === 'call' && x.e.recv && isId(x.e.recv, n) && ['put', 'add', 'insert', 'emplace', 'append'].includes(x.e.m)) written = true; });
        const used = idsIn(last.v).has(n);
        if (written && used) return { kind: 'table', name: n, text: `\`${n}\` is a lookup table: the function returns the stored answer if it exists, and stores every new answer` };
      }
    }
    return null;
  };
  P.memoPlan = function (fn, env, info, own, params, memo) {
    const line = fn.line;
    let states = ONE; const parts = [];
    for (const q of params) {
      const rec = env.get(q.p.n);
      if (q.kind === 'same') { continue; }
      if (q.kind === 'dec' || q.kind === 'dec-mixed') {
        const b = this.baseBounds(fn, q.p, info);
        if (!b.lower) throw new Und(`\`${q.p.n}\` decreases but no base case that stops it was found`, line, 'recursion');
        if (q.forms.some((f) => f.varStep)) this.assume(`The amount subtracted from \`${q.p.n}\` is non-negative (so the number of distinct values of \`${q.p.n}\` is bounded by its starting value).`);
        const r = A.add(this.initMag(rec, line), ONE); states = A.mul(states, r); parts.push(`${q.p.n} takes ≤ ${strip(this.fmt(r))} values (counts down from its start)`);
      } else if (q.kind === 'inc') {
        const b = this.baseBounds(fn, q.p, info);
        if (!b.upper) throw new Und(`\`${q.p.n}\` grows but no limit that stops it was found`, line, 'recursion');
        const r = A.add(A.add(this.mag(b.upper, env, line), this.initMag(rec, line)), ONE); states = A.mul(states, r); parts.push(`${q.p.n} takes ≤ ${strip(this.fmt(r))} values (counts up to \`${show(b.upper)}\`)`);
      } else throw new Und(`parameter \`${q.p.n}\` changes in a way (${show(q.forms[0].e || {})}) that does not let the number of distinct states be bounded`, line, 'recursion');
    }
    if (!parts.length) throw new Und('could not find a parameter whose values bound the number of distinct states', line, 'recursion');
    return { kind: 'memoization', time: A.mul(states, own), depth: A.add(states.length === 1 ? ONE : ONE, this.recDepthMemo(params, env, line)), calls: states, why: `${memo.text}. Each distinct state is computed once: ${parts.join('; ')} → at most ${strip(this.fmt(states))} states, each costing ${this.fmt(own)} outside the recursive calls (cached calls return immediately)`, tableSpace: states, depthWhy: 'depth ≤ the longest chain of states' };
  };
  P.recDepthMemo = function (params, env, line) {
    let d = ONE;
    for (const q of params) { if (q.kind === 'same') continue; const rec = env.get(q.p.n); d = A.add(d, this.initMag(rec, line)); }
    return d;
  };

  // ------------------------------------------------------------------ extras used by core
  P.dataVal = function (kind, container, env, line) {
    const nm = show(container);
    if (kind === 'max') return this.pSym(`max:${nm}`, 'val', `largest value in \`${nm}\``, 'M', 'largest value');
    return this.pSym(`sum:${nm}`, 'val', `sum of the values in \`${nm}\``, 'S', 'sum');
  };

  // ------------------------------------------------------------------ space
  P.returnedNames = function (fn) {
    const out = new Set();
    const add = (e) => { if (!e) return; if (e.t === 'id') out.add(e.n); else if (e.t === 'lit' || e.t === 'tuple') e.a.forEach(add); else if (e.t === 'new') e.a.forEach(add); else if (e.t === 'op' && e.o === '?:') { add(e.a[1]); add(e.a[2]); } };
    eachStmt(fn.body, (s) => { if (s.s === 'return') add(s.v); });
    return out;
  };
  P.spaceTotal = function (depthMult, fn) {
    void fn;
    try {
      let t = ONE; const parts = [];
      const outs = this.returnedNames(this.fr.fn); const outputs = [];
      for (const { rec, line } of this.fr.locals || []) {
        if (rec.aliasOf) continue;
        if (outs.has(rec.name)) { try { outputs.push({ name: rec.name, line, bound: this.totalBound(rec) }); } catch (e) { void e; } continue; }
        if (rec.initErr) throw new Und(`cannot bound the size of local \`${rec.name}\`: ${rec.initErr}`, line);
        if (!rec.init && !(this.growthList(rec).length)) continue;
        const b = this.totalBound(rec);
        parts.push({ name: rec.name, line, bound: b });
        t = A.add(t, b);
      }
      for (const c of this.fr.calleeSpace || []) t = A.add(t, c);
      for (const tm of this.fr.temps || []) { t = A.add(t, tm.size); parts.push({ name: tm.what, line: tm.line, bound: tm.size, temp: true }); }
      if (this.fr.tempErr) throw this.fr.tempErr;
      return { total: A.mul(t, depthMult), parts, outputs };
    } catch (err) { if (err instanceof Und) return { err }; throw err; }
  };
}
