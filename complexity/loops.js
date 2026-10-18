// Loop analysis: every loop must match a template whose preconditions are checked on the code, otherwise `Und`.
import * as A from './algebra.js';
import { Und, eachExpr, eachStmt, eachStmtExprs, eqE, idsIn, mentions, show } from './util.js';
import { isContainer } from './core.js';

const { ONE } = A;
const EXIT = new Set(['break', 'return', 'throw']);
const POPS = new Set(['pop', 'popleft', 'poll', 'pop_back', 'pop_front', 'pollFirst', 'pollLast', 'removeFirst', 'removeLast', 'remove', 'dequeue', 'take']);
const ADJ_GET = new Set(['get', 'at', 'getOrDefault']);

// ------------------------------------------------------------------ static helpers over the IR
export const num = (e) => (e && e.t === 'num' ? e.v : (e && e.t === 'op' && e.o === 'neg' && e.a[0].t === 'num' ? -e.a[0].v : null));
const isId = (e, n) => e && e.t === 'id' && (n === undefined || e.n === n);

/** all simple statements' expressions in a statement list, not descending into nested loops when `skipLoops` */
function simpleExprs(s) {
  switch (s.s) {
    case 'decl': return [s.init];
    case 'assign': return [{ t: 'assign', op: s.op, target: s.target, v: s.v }];
    case 'expr': return [s.e];
    case 'return': return [s.v];
    case 'del': return [s.target];
    default: return [];
  }
}
export function declaredNames(stmts) { const out = new Set(); eachStmt(stmts, (s) => { if (s.s === 'decl') out.add(s.n); }); return out; }

/** how a statement changes variable `name`: list of {kind: add|mul|div|other, c} */
export function updatesInExpr(e, name) {
  const out = [];
  eachExpr(e, (x) => {
    if (x.t === 'incdec' && isId(x.target, name)) out.push({ kind: 'add', c: x.op === '++' ? 1 : -1 });
    else if (x.t === 'assign' && isId(x.target, name)) {
      const c = num(x.v);
      switch (x.op) {
        case '+=': out.push(c !== null ? { kind: 'add', c } : { kind: 'other' }); break;
        case '-=': out.push(c !== null ? { kind: 'add', c: -c } : { kind: 'other' }); break;
        case '*=': out.push(c !== null && c >= 2 ? { kind: 'mul', c } : { kind: 'other' }); break;
        case '<<=': out.push(c !== null && c >= 1 ? { kind: 'mul', c: 2 } : { kind: 'other' }); break;
        case '/=': case '//=': out.push(c !== null && c >= 2 ? { kind: 'div', c } : { kind: 'other' }); break;
        case '>>=': out.push(c !== null && c >= 1 ? { kind: 'div', c: 2 } : { kind: 'other' }); break;
        case '=': {
          const v = x.v;
          if (v.t === 'op' && v.a.length === 2 && isId(v.a[0], name) && num(v.a[1]) !== null) {
            const k = num(v.a[1]);
            if (v.o === '+') out.push({ kind: 'add', c: k }); else if (v.o === '-') out.push({ kind: 'add', c: -k });
            else if (v.o === '*' && k >= 2) out.push({ kind: 'mul', c: k });
            else if ((v.o === '/' || v.o === '//') && k >= 2) out.push({ kind: 'div', c: k });
            else if (v.o === '>>' && k >= 1) out.push({ kind: 'div', c: 2 });
            else if (v.o === '<<' && k >= 1) out.push({ kind: 'mul', c: 2 });
            else out.push({ kind: 'other' });
          } else if (v.t === 'op' && v.o === '+' && v.a.length === 2 && isId(v.a[1], name) && num(v.a[0]) !== null) out.push({ kind: 'add', c: num(v.a[0]) });
          else out.push({ kind: 'other' });
          break;
        }
        default: out.push({ kind: 'other' });
      }
    }
  });
  return out;
}
/** updates of `name` anywhere in a statement list (including nested statements and Python tuple targets) */
export function updatesOf(stmts, name) {
  const out = [];
  eachStmt(stmts, (s) => {
    if (s.s === 'assign' && s.target.t === 'tuple') { if (s.target.a.some((x) => isId(x, name))) out.push({ kind: 'other', stmt: s }); return; }
    if (s.s === 'assign') { for (const u of updatesInExpr({ t: 'assign', op: s.op, target: s.target, v: s.v }, name)) out.push({ ...u, stmt: s }); return; }
    if (s.s === 'decl') { if (s.n === name) out.push({ kind: 'other', stmt: s }); if (s.init) for (const u of updatesInExpr(s.init, name)) out.push({ ...u, stmt: s }); return; }
    if (s.s === 'for') { if ((s.vars || []).includes(name)) out.push({ kind: 'other', stmt: s }); if (s.cond) for (const u of updatesInExpr(s.cond, name)) out.push({ ...u, stmt: s }); return; }
    if (s.s === 'del') { if (isId(s.target, name)) out.push({ kind: 'other', stmt: s }); return; }
    for (const e of s.s === 'if' || s.s === 'while' ? [s.cond] : s.s === 'expr' ? [s.e] : s.s === 'return' ? [s.v] : s.s === 'switch' ? [s.disc] : []) for (const u of updatesInExpr(e, name)) out.push({ ...u, stmt: s });
  });
  return out;
}
export function assignedNames(stmts) {
  const names = new Set();
  const addT = (t) => { if (!t) return; if (t.t === 'id') names.add(t.n); else if (t.t === 'tuple') t.a.forEach(addT); };
  const scan = (e) => eachExpr(e, (x) => { if ((x.t === 'assign' || x.t === 'incdec')) addT(x.target); });
  eachStmt(stmts, (s) => {
    if (s.s === 'assign') { addT(s.target); scan(s.v); } else if (s.s === 'decl') { names.add(s.n); scan(s.init); } else if (s.s === 'expr') scan(s.e); else if (s.s === 'return') scan(s.v);
    else if (s.s === 'if' || s.s === 'while') scan(s.cond); else if (s.s === 'for') { (s.vars || []).forEach((n) => names.add(n)); scan(s.cond); } else if (s.s === 'del') addT(s.target);
  });
  return names;
}
export function stmtHasUpdate(s, name, kinds = null) {
  for (const e of simpleExprs(s)) for (const u of updatesInExpr(e, name)) if (!kinds || kinds.includes(u.kind)) return true;
  if (s.s === 'assign' && s.target.t === 'tuple' && s.target.a.some((x) => isId(x, name))) return true;
  return false;
}
/** every path through `stmts` that continues the loop makes progress (pred is true for some statement on the path) */
export function progressOnAll(stmts, pred) {
  const go = (list, done) => {
    let ok = true;
    for (const s of list) {
      if (EXIT.has(s.s)) return { ok, done, term: true };
      if (s.s === 'continue') return { ok: ok && done, done, term: true };
      if (s.s === 'if') {
        const a = go(s.then, done), b = go(s.else || [], done);
        ok = ok && a.ok && b.ok;
        const fa = a.term || a.done, fb = b.term || b.done;
        if (a.term && b.term) return { ok, done, term: true };
        done = fa && fb;
        if (pred(s, 'cond')) done = true;
      } else if (s.s === 'try') { const a = go(s.body, done); ok = ok && a.ok; done = a.done || a.term; }
      else if (s.s === 'switch') { /* conservative: cases do not count */ }
      else if (s.s === 'while' || s.s === 'for') { if (s.doWhile && pred(s)) done = true; }
      else if (pred(s)) done = true;
    }
    return { ok, done, term: false };
  };
  const r = go(stmts, false);
  return r.ok && (r.done || r.term);
}
const exprHasCall = (e, f) => { let r = false; eachExpr(e, (x) => { if (f(x)) r = true; }); return r; };
export function stmtPops(s, qname) {
  for (const e of simpleExprs(s)) if (e && exprHasCall(e, (x) => x.t === 'call' && ((x.recv && isId(x.recv, qname) && POPS.has(x.m) && (x.m !== 'remove' || x.a.length === 0)) || (!x.recv && /^(heapq\.)?heappop$/.test(x.fn || '') && x.a[0] && isId(x.a[0], qname))))) return true;
  return false;
}
export function conjuncts(c, op = '&&') { return c && c.t === 'op' && c.o === op ? c.a.flatMap((x) => conjuncts(x, op)) : [c]; }
const flip = { '<': '>', '<=': '>=', '>': '<', '>=': '<=', '!=': '!=', '==': '==' };
/** `i < n`  ->  {v:'i', op:'<', bound:n}; also `n > i` */
export function cmpOf(c, wantVar = null) {
  if (!c || c.t !== 'op' || !flip[c.o] || c.a.length !== 2) return null;
  const [a, b] = c.a;
  if (a.t === 'op' && (a.o === '+' || a.o === '-') && a.a[0].t === 'id' && num(a.a[1]) !== null && (!wantVar || a.a[0].n === wantVar)) return { v: a.a[0].n, op: c.o, bound: b, off: a.o === '+' ? num(a.a[1]) : -num(a.a[1]) };
  if (a.t === 'id' && (!wantVar || a.n === wantVar)) return { v: a.n, op: c.o, bound: b };
  if (b.t === 'id' && (!wantVar || b.n === wantVar)) return { v: b.n, op: flip[c.o], bound: a };
  return null;
}
export const asgOf = (st) => (st.s === 'assign' ? { target: st.target, op: st.op, v: st.v } : st.s === 'expr' && st.e && st.e.t === 'assign' ? { target: st.e.target, op: st.e.op, v: st.e.v } : null);
const sameAs = (e, f) => eqE(e, f);

export function installLoops(C) {
  const P = C.prototype;

  P.pushLoop = function (trips, extra = {}) { this.fr.loops.push({ trips, ...extra }); };
  P.popLoop = function () { return this.fr.loops.pop(); };
  const nodeText = (s) => {
    if (s.s === 'while') return `while (${show(s.cond)})`;
    if (s.mode === 'c') return `for (…; ${show(s.cond)}; …)`;
    if (s.mode === 'range') return `for ${(s.vars || []).join(', ')} in range(${[s.lo, s.hi, s.step].filter(Boolean).map((x) => show(x)).join(', ')})`;
    return `for ${(s.vars || []).join(', ')} in ${show(s.iter)}`;
  };

  // ------------------------------------------------------------------ for
  P.forStmt = function (s, env) {
    const line = s.line;
    if (s.mode === 'range') {
      const iter = { t: 'call', fn: 'range', a: s.lo ? [s.lo, s.hi] : [s.hi], line };
      if (s.step) iter.step = s.step;
      return this.eachLoop(s, { ...s, mode: 'each', iter, rangeStep: s.step }, env);
    }
    if (s.mode === 'each') return this.eachLoop(s, s, env);
    return this.cLoop(s, env);
  };

  P.eachLoop = function (s0, s, env) {
    const line = s.line;
    const nd = this.node('loop', line, nodeText(s0));
    return this.within(nd, () => {
      let hdr = this.ec(s.iter, env);
      if (s.rangeStep) hdr = A.add(hdr, this.ec(s.rangeStep, env));
      const inner = env; // loop variables live in the function scope
      // amortised iteration over the row of a distinct key (graph adjacency lists)
      const am = this.amortRow(s.iter, env, line);
      let trips, why;
      if (am) { trips = am.total; why = am.why; } else { trips = this.iterTrips(s.iter, env, line); why = this.tripsWhy(s.iter, env, trips); }
      this.bindLoopVars(s.vars || [], s.iter, inner, trips, line);
      if (nd) { nd.trips = trips; nd.why = why; if (am) nd.amortized = true; }
      this.pushLoop(trips, am ? { global: true } : {});
      let body;
      try { body = this.block(s.body, inner); } finally { this.popLoop(); }
      const per = A.add(body, ONE);
      let total;
      if (am) { this.pushGlobal(A.mul(trips, per), line, `${nodeText(s0)} (amortised)`); total = A.add(hdr, ONE); } else total = A.add(hdr, A.mul(trips, per));
      if (nd) { nd.body = per; nd.cost = total; }
      return total;
    });
  };

  P.tripsWhy = function (iter, env, trips) {
    if (iter.t === 'call' && !iter.recv && iter.fn === 'range') return `\`range(${iter.a.map((x) => show(x)).join(', ')})\` yields at most ${this.fmt(trips).replace(/^O\(|\)$/g, '')} values`;
    return `it visits every element of \`${show(iter)}\` once (${this.fmt(trips).replace(/^O\(|\)$/g, '')} elements)`;
  };

  /** declare the loop variables with whatever is known about their values / sizes */
  P.bindLoopVars = function (vars, iter, env, trips, line) {
    const mk = (name, rec) => env.set(name, { name, isParam: false, ownerFn: this.fr.fnKey, depth: this.fr.loops.length, line, loopVar: true, ...rec });
    const unwrap = (it, vs) => {
      if (it.t === 'call' && !it.recv) {
        const f = it.fn;
        if (f === 'range') {
          let val; try { val = this.sizeOf(it, env, line); } catch (err) { if (!(err instanceof Und)) throw err; val = undefined; }
          const rec = { ty: { k: 'int' }, val, noVal: val ? undefined : 'the range bound depends on data' };
          if (vs[0]) mk(vs[0], rec); vs.slice(1).forEach((n) => mk(n, { ty: { k: 'unknown' } }));
          return;
        }
        if (f === 'enumerate') { if (vs[0]) mk(vs[0], { ty: { k: 'int' }, val: trips }); unwrap(it.a[0], vs.slice(1)); return; }
        if (f === 'zip') { vs.forEach((n, i) => { if (it.a[i]) unwrap(it.a[i], [n]); else mk(n, { ty: { k: 'unknown' } }); }); return; }
        if (['reversed', 'sorted', 'list', 'tuple', 'set', 'iter', 'frozenset'].includes(f) && it.a.length) return unwrap(it.a[0], vs);
      }
      if (it.t === 'call' && it.recv && ['items', 'entrySet'].includes(it.m)) {
        const t = this.typeOf(it.recv, env);
        if (vs.length >= 2) { mk(vs[0], { ty: t.key || { k: 'unknown' } }); mk(vs[1], this.elemRec(t.e, it.recv, env)); } else vs.forEach((n) => mk(n, { ty: { k: 'unknown' } }));
        return;
      }
      if (it.t === 'call' && it.recv && ['keys', 'keySet'].includes(it.m)) { const t = this.typeOf(it.recv, env); vs.forEach((n) => mk(n, { ty: t.key || { k: 'unknown' } })); return; }
      if (it.t === 'call' && it.recv && ['values'].includes(it.m)) { const t = this.typeOf(it.recv, env); vs.forEach((n) => mk(n, this.elemRec(t.e, it.recv, env))); return; }
      const t = this.typeOf(it, env);
      if (vs.length === 1) {
        let et = t.e || { k: 'unknown' };
        if (t.k === 'str') et = { k: 'str' };
        if (t.k === 'map' || t.k === 'sortedmap') et = t.key || { k: 'unknown' };
        mk(vs[0], this.elemRec(et, it, env, t));
      } else vs.forEach((n) => mk(n, { ty: { k: 'unknown' } }));
    };
    unwrap(iter, [...vars]);
  };
  /** record for the elements of a container expression */
  P.elemRec = function (et, containerExpr, env, ct) {
    const rec = { ty: et || { k: 'unknown' } };
    if (ct && ct.k === 'str') { rec.init = ONE; return rec; }
    if (isContainer(rec.ty) || rec.ty.k === 'unknown') {
      const root = this.rootVar(containerExpr); const v = root && env.get(root.n);
      if (v && v.inner && containerExpr.t === 'id') rec.init = v.inner;
      else if (v && v.inner2) rec.init = v.inner2;
      else if (v && v.isParam && containerExpr.t === 'id' && v.ty && v.ty.e && isContainer(v.ty.e)) { rec.init = this.sizeOf({ t: 'idx', o: containerExpr, i: { t: 'num', v: 0 } }, env, 0); }
      if (isContainer(rec.ty) && rec.init) rec.fromRow = true;
    }
    return rec;
  };

  // ------------------------------------------------------------------ amortised row loops (distinct keys)
  /** `for v in graph[u]` where u is a distinct key: all executions together touch each row once -> total size of graph */
  P.amortRow = function (iter, env, line) {
    const info = this.rowAccess(iter, env);
    if (!info) return null;
    if (!this.fr.distinct || !this.fr.distinct.has(info.key)) return null;
    const g0 = env.get(info.rootName);
    if (!g0) return null;
    const g = this.growthTarget(g0);
    const gt = this.typeOf({ t: 'id', n: info.rootName }, env);
    if (!(isContainer(gt) && (gt.k === 'map' || gt.k === 'sortedmap' || gt.e && (isContainer(gt.e) || gt.e.k === 'unknown')))) return null;
    let total;
    if (g.isParam) { this.needSize(g, line); total = this.pSym(`E:${g.name}`, 'tot', `total number of entries in all rows of \`${g.name}\``, 'E', 'total entries', g.name); }
    else total = this.totalBound(g);
    return { total, why: `\`${show(iter)}\` is read once for every distinct \`${info.key}\`, so over the whole run each row of \`${info.rootName}\` is scanned at most once: total ≤ ${this.fmt(total).replace(/^O\(|\)$/g, '')} entries` };
  };
  P.rowAccess = function (it, env) {
    let e = it;
    if (e.t === 'call' && e.recv && ['items', 'iterator', 'stream', 'keySet', 'values'].includes(e.m)) e = e.recv;
    if (e.t === 'idx' && e.o.t === 'id' && e.i.t === 'id') return { rootName: e.o.n, key: e.i.n };
    if (e.t === 'call' && e.recv && e.recv.t === 'id' && ADJ_GET.has(e.m) && e.a[0] && e.a[0].t === 'id') return { rootName: e.recv.n, key: e.a[0].n };
    return null;
  };

  // ------------------------------------------------------------------ C-style for
  P.cLoop = function (s, env) {
    const line = s.line;
    const nd = this.node('loop', line, nodeText(s));
    return this.within(nd, () => {
      let hdr = this.block(s.init, env);
      const plan = this.countingPlan(s.cond, s.body, s.update, env, line, true, s);
      if (nd) { nd.trips = plan.trips; nd.why = plan.why; }
      const per = this.runBodyInLoop(plan.trips, () => A.add(A.add(this.block(s.body, env), s.cond ? this.ec(s.cond, env) : ONE), this.block(s.update, env)));
      const total = A.add(hdr, A.mul(plan.trips, per));
      if (nd) { nd.body = per; nd.cost = total; }
      return total;
    });
  };
  P.runBodyInLoop = function (trips, f, extra = {}) { this.pushLoop(trips, extra); try { return f(); } finally { this.popLoop(); } };

  /** value information of a variable at loop entry */
  P.initMag = function (v, line) {
    if (v.isParam) return this.needVal(v, line);
    if (v.val) return v.val;
    throw new Und(v.noVal || `the starting value of \`${v.name}\` cannot be bounded`, line);
  };

  /**
   * Counting loops. `cond` is the loop condition, `body` its statements, `update` the for-update statements (C-style).
   * Returns {trips, why}.
   */
  P.countingPlan = function (cond, body, update, env, line, isFor, s) {
    if (!cond) throw new Und('a `for` loop without a condition runs until a `break` — the number of iterations cannot be determined from the code', line, 'loop');
    const assigned = assignedNames(body);
    const tries = [];
    for (const c of conjuncts(cond)) {
      // i*i <= n
      if (c.t === 'op' && ['<', '<=', '>', '>='].includes(c.o) && c.a[0].t === 'op' && c.a[0].o === '*' && isId(c.a[0].a[0]) && sameAs(c.a[0].a[0], c.a[0].a[1])) {
        const v = c.a[0].a[0].n; tries.push({ kind: 'sq', v, op: c.o, bound: c.a[1] }); continue;
      }
      if (c.t === 'id') { tries.push({ kind: 'truthy', v: c.n }); continue; }
      const cm = cmpOf(c);
      if (cm) tries.push({ kind: 'cmp', ...cm });
    }
    const reasons = [];
    for (const t of tries) {
      const rec = env.get(t.v);
      if (!rec) { reasons.push(`\`${t.v}\` is not a known variable`); continue; }
      const ups = [...updatesOf(update || [], t.v), ...updatesOf(body, t.v)];
      if (!ups.length) { reasons.push(`\`${t.v}\` is never updated in the loop`); continue; }
      if (ups.some((u) => u.kind === 'other')) { reasons.push(`\`${t.v}\` is changed in a way the analyzer cannot follow (not a constant step)`); continue; }
      const kinds = new Set(ups.map((u) => u.kind));
      if (kinds.size > 1) { reasons.push(`\`${t.v}\` is changed by different kinds of steps`); continue; }
      const kind = [...kinds][0];
      if (!isFor || !(update && updatesOf(update, t.v).length)) { if (!progressOnAll(body, (st) => stmtHasUpdate(st, t.v))) { reasons.push(`some path through the loop body does not change \`${t.v}\`, so progress is not guaranteed`); continue; } }
      if (t.kind === 'cmp' || t.kind === 'sq') {
        const bound = t.bound;
        const bids = idsIn(bound);
        const moved = [...bids].filter((n) => assigned.has(n) && !(env.get(n) && isContainer(env.get(n).ty)));
        if (moved.length) { reasons.push(`the bound \`${show(bound)}\` changes inside the loop (\`${moved[0]}\`)`); continue; }
        if (kind === 'add') {
          const dir = ups.every((u) => u.c > 0) ? 1 : ups.every((u) => u.c < 0) ? -1 : 0;
          if (!dir) { reasons.push(`\`${t.v}\` moves in both directions`); continue; }
          if (t.kind === 'sq') {
            if (dir !== 1 || !(t.op === '<' || t.op === '<=')) { reasons.push('unsupported square-root loop'); continue; }
            const st = rec.isParam ? null : rec.cst;
            if (rec.cst === undefined && !rec.isParam) { reasons.push(`the start of \`${t.v}\` is not a constant`); continue; }
            void st;
            const b = this.mag(bound, env, line); const r = A.sqrtE(b);
            if (!r) { reasons.push('square root of a non-simple bound'); continue; }
            return { trips: A.add(r, ONE), why: `\`${t.v}\` goes up by ${ups[0].c} while \`${t.v}·${t.v} ${t.op} ${show(bound)}\`, so it stops after about √(${this.fmt(b).replace(/^O\(|\)$/g, '')}) steps` };
          }
          if (dir === 1 && (t.op === '<' || t.op === '<=' || (t.op === '!=' && ups.every((u) => u.c === 1)))) {
            const init = this.initMag(rec, line);
            const b = this.mag(bound, env, line);
            const trips = A.add(b, init);
            return { trips, why: `\`${t.v}\` starts at ${this.fmt(init).replace(/^O\(|\)$/g, '')} and goes up by ${Math.min(...ups.map((u) => u.c))}${ups.some((u) => u.c !== ups[0].c) ? '+' : ''} until it reaches \`${show(bound)}\` (≈ ${this.fmt(b).replace(/^O\(|\)$/g, '')}), so at most ${this.fmt(trips).replace(/^O\(|\)$/g, '')} iterations` };
          }
          if (dir === -1 && (t.op === '>' || t.op === '>=' || (t.op === '!=' && ups.every((u) => u.c === -1)))) {
            const init = this.initMag(rec, line);
            const b = this.mag(bound, env, line);
            const trips = A.add(b, init);
            return { trips, why: `\`${t.v}\` starts at ${this.fmt(init).replace(/^O\(|\)$/g, '')} and goes down by ${Math.min(...ups.map((u) => -u.c))}${ups.some((u) => u.c !== ups[0].c) ? '+' : ''} until it passes \`${show(bound)}\`, so at most ${this.fmt(trips).replace(/^O\(|\)$/g, '')} iterations` };
          }
          reasons.push(`\`${t.v}\` moves away from the bound in \`${show(cond)}\``); continue;
        }
        if (kind === 'mul' && (t.op === '<' || t.op === '<=')) {
          if (!(rec.cst !== undefined && rec.cst >= 1)) { reasons.push(`\`${t.v}\` is multiplied each step, but its starting value is not a constant ≥ 1 (a start of 0 would never grow)`); continue; }
          const b = this.mag(bound, env, line);
          return { trips: A.add(A.logE(b), ONE), why: `\`${t.v}\` doubles (×${ups[0].c}) each iteration from ${rec.cst} until it reaches \`${show(bound)}\` ≈ ${this.fmt(b).replace(/^O\(|\)$/g, '')}: that takes about log(${this.fmt(b).replace(/^O\(|\)$/g, '')}) iterations` };
        }
        if (kind === 'div' && (t.op === '>' || t.op === '>=' || t.op === '!=')) {
          const k = num(bound);
          const trunc = this.lang !== 'python';
          if (k === null || k < 0 || (t.op === '!=' && !(trunc && k === 0))) { reasons.push(`the stopping value \`${show(bound)}\` is not a non-negative constant`); continue; }
          const init = this.initMag(rec, line);
          return { trips: A.add(A.logE(init), ONE), why: `\`${t.v}\` is divided by ${ups[0].c} each iteration until it drops to ${k}, so it runs about log(${this.fmt(init).replace(/^O\(|\)$/g, '')}) times` };
        }
        reasons.push(`the update of \`${t.v}\` does not move it toward the bound of \`${show(cond)}\``); continue;
      }
      if (t.kind === 'truthy' && kind === 'div') {
        const init = this.initMag(rec, line);
        if (this.lang === 'python' && false) continue;
        return { trips: A.add(A.logE(init), ONE), why: `\`${t.v}\` is divided by ${ups[0].c} each iteration until it reaches 0: about log(${this.fmt(init).replace(/^O\(|\)$/g, '')}) iterations` };
      }
    }
    if (!isFor) return null;
    throw new Und(`the number of iterations of this loop cannot be proven${reasons.length ? ': ' + reasons[0] : ` from \`${show(cond)}\``}`, line, 'loop');
  };

  // ------------------------------------------------------------------ while
  P.whileStmt = function (s, env) {
    const line = s.line;
    const nd = this.node('loop', line, nodeText(s));
    return this.within(nd, () => {
      const condCost = this.ec(s.cond, env);
      const plan = this.whilePlan(s, env, line);
      if (nd) { nd.trips = plan.trips; nd.why = plan.why; nd.template = plan.template; if (plan.global) nd.amortized = true; }
      const run = () => A.add(this.block(s.body, env), A.add(condCost, ONE));
      let per;
      const prevPop = this.fr.popVars; const prevDistinct = this.fr.distinct;
      if (plan.setup) plan.setup();
      try { per = this.runBodyInLoop(plan.trips, run, plan.global ? { global: true } : {}); } finally { if (plan.teardown) plan.teardown(); this.fr.popVars = prevPop; this.fr.distinct = prevDistinct; }
      let total;
      if (plan.global) { this.pushGlobal(A.mul(plan.trips, per), line, 'while loop (amortised)'); total = ONE; } else total = A.mul(plan.trips, per);
      total = A.add(total, condCost);
      if (plan.extraCost) total = A.add(total, plan.extraCost);
      if (nd) { nd.body = per; nd.cost = total; }
      return total;
    });
  };

  P.whilePlan = function (s, env, line) {
    const body = s.body;
    const failures = [];
    const tryT = (name, f) => { try { const r = f(); if (r) { r.template = name; return r; } } catch (err) { if (!(err instanceof Und)) throw err; failures.push(err); } return null; };
    if (s.doWhile) failures.push(new Und('do-while loops are only supported when the condition is a simple counter test', line));
    const cands = [];
    for (const [name, f] of [['counting', () => this.countingPlan(s.cond, body, null, env, line, false, s)], ['two-pointer', () => this.twoPointerPlan(s, env, line)], ['binary-search', () => this.binarySearchPlan(s, env, line)], ['euclid', () => this.euclidPlan(s, env, line)], ['pointer-walk', () => this.pointerWalkPlan(s, env, line)], ['monotone-pointer', () => this.monotonePointerPlan(s, env, line)], ['drain', () => this.drainPlan(s, env, line)]]) {
      const p = tryT(name, f);
      if (p) cands.push(p);
    }
    // several templates may prove a bound: keep the tightest (smallest total number of iterations over the whole run)
    const total = (p) => (p.global ? p.trips : A.mul(this.multSince(0), p.trips));
    let plan = null;
    for (const p of cands) { if (!plan || (A.geq(total(plan), total(p)) && !A.eq(total(plan), total(p)))) plan = p; }
    if (plan) return plan;
    const f = failures.find((x) => x.hint !== 'soft') || failures[0];
    throw new Und(`the number of iterations of \`while (${show(s.cond)})\` cannot be proven${f ? ': ' + f.reason : ''}`, line, 'loop');
  };

  /** a < b, with a only moving up and b only moving down */
  P.twoPointerPlan = function (s, env, line) {
    for (const c of conjuncts(s.cond)) {
      const cm = c.t === 'op' && ['<', '<=', '>', '>=', '!='].includes(c.o) && c.a[0].t === 'id' && c.a[1].t === 'id' ? { a: c.a[0].n, b: c.a[1].n, op: c.o } : null;
      if (!cm) continue;
      let lo = cm.a, hi = cm.b;
      if (cm.op === '>' || cm.op === '>=') { lo = cm.b; hi = cm.a; }
      const ul = updatesOf(s.body, lo), uh = updatesOf(s.body, hi);
      if ([...ul, ...uh].some((u) => u.kind !== 'add')) continue;
      if (!ul.every((u) => u.c > 0) || !uh.every((u) => u.c < 0)) continue;
      if (cm.op === '!=' && (ul.some((u) => u.c !== 1) || uh.some((u) => u.c !== -1) || (ul.length && uh.length))) continue;
      if (!ul.length && !uh.length) continue;
      if (!progressOnAll(s.body, (st) => stmtHasUpdate(st, lo) || stmtHasUpdate(st, hi))) continue;
      const rl = env.get(lo), rh = env.get(hi);
      if (!rl || !rh) continue;
      const trips = A.add(this.initMag(rl, line), this.initMag(rh, line));
      return { trips, why: `\`${lo}\` only moves up and \`${hi}\` only moves down, and every iteration moves at least one of them, so the gap \`${hi} − ${lo}\` (at most ${this.fmt(trips).replace(/^O\(|\)$/g, '')}) shrinks by ≥ 1 each time` };
    }
    return null;
  };

  /** lo / hi / mid halving */
  P.binarySearchPlan = function (s, env, line) {
    for (const c of conjuncts(s.cond)) {
      const cm = c.t === 'op' && ['<', '<=', '>', '>='].includes(c.o) && c.a[0].t === 'id' && c.a[1].t === 'id' ? c : null;
      if (!cm) continue;
      let lo = c.a[0].n, hi = c.a[1].n, strict = c.o === '<' || c.o === '>';
      if (c.o === '>' || c.o === '>=') { lo = c.a[1].n; hi = c.a[0].n; }
      // find `mid = (lo + hi) / 2` style definition
      let mid = null;
      eachStmt(s.body, (st) => {
        const a0 = asgOf(st);
        const t = st.s === 'decl' ? { t: 'id', n: st.n } : a0 && a0.op === '=' && a0.target.t === 'id' ? a0.target : null;
        const v = st.s === 'decl' ? st.init : a0 ? a0.v : null;
        if (t && v && this.isMidpoint(v, lo, hi)) mid = mid || t.n;
      });
      if (!mid) continue;
      // every assignment to lo / hi must be a halving update, and all paths must shrink the interval or exit
      const ul = updatesOf(s.body, lo), uh = updatesOf(s.body, hi);
      let ok = true;
      const okLo = (st) => { const a = asgOf(st); return a && a.op === '=' && isId(a.target, lo) && this.offsetOf(a.v, mid) >= 1; };
      const okHi = (st) => { const a = asgOf(st); return a && a.op === '=' && isId(a.target, hi) && (this.offsetOf(a.v, mid) <= -1 || (strict && isId(a.v, mid))); };
      for (const u of ul) if (!okLo(u.stmt)) ok = false;
      for (const u of uh) if (!okHi(u.stmt)) ok = false;
      if (!ok) continue;
      const midOf = (e) => e;
      void midOf;
      const shrinks = progressOnAll(s.body, (st) => okLo(st) || okHi(st));
      if (!shrinks) continue;
      const rl = env.get(lo), rh = env.get(hi);
      if (!rl || !rh) continue;
      const span = A.add(this.initMag(rl, line), this.initMag(rh, line));
      return { trips: A.add(A.logE(span), ONE), why: `each iteration moves \`${lo}\` past \`${mid}\` or \`${hi}\` before \`${mid}\`, discarding at least half of the interval of size ≈ ${this.fmt(span).replace(/^O\(|\)$/g, '')}, so it runs at most log(${this.fmt(span).replace(/^O\(|\)$/g, '')}) + 1 times` };
    }
    return null;
  };
  P.isMidpoint = function (v, lo, hi) {
    const L = { t: 'id', n: lo }, H = { t: 'id', n: hi };
    const half = (e) => e.t === 'op' && (e.o === '/' || e.o === '//') && num(e.a[1]) === 2 || e.t === 'op' && e.o === '>>' && num(e.a[1]) === 1;
    const sum = (e) => e.t === 'op' && e.o === '+' && ((eqE(e.a[0], L) && eqE(e.a[1], H)) || (eqE(e.a[0], H) && eqE(e.a[1], L)));
    const diff = (e) => e.t === 'op' && e.o === '-' && eqE(e.a[0], H) && eqE(e.a[1], L);
    if (half(v) && sum(v.a[0])) return true;
    if (v.t === 'op' && v.o === '+' && eqE(v.a[0], L) && half(v.a[1]) && diff(v.a[1].a[0])) return true;
    if (v.t === 'op' && v.o === '+' && half(v.a[0]) && diff(v.a[0].a[0]) && eqE(v.a[1], L)) return true;
    return false;
  };
  /** `mid + 1` -> 1, `mid - 1` -> -1, `mid` -> 0, otherwise null */
  P.offsetOf = function (v, mid) {
    if (isId(v, mid)) return 0;
    if (v.t === 'op' && (v.o === '+' || v.o === '-') && isId(v.a[0], mid) && num(v.a[1]) !== null) return v.o === '+' ? num(v.a[1]) : -num(v.a[1]);
    return null;
  };

  /** while (b) { t = b; b = a % b; a = t }  or  a, b = b, a % b */
  P.euclidPlan = function (s, env, line) {
    const cm = cmpOf(s.cond);
    const bn = s.cond.t === 'id' ? s.cond.n : cm && num(cm.bound) === 0 && ['!=', '>'].includes(cm.op) ? cm.v : null;
    if (!bn) return null;
    const stmts = s.body;
    let an = null;
    if (stmts.length === 1 && stmts[0].s === 'assign' && stmts[0].target.t === 'tuple' && stmts[0].v.t === 'lit' && stmts[0].v.kind === 'tuple') {
      const [t0, t1] = stmts[0].target.a; const [v0, v1] = stmts[0].v.a;
      if (isId(t0) && isId(t1, bn) && isId(v0, bn) && v1.t === 'op' && v1.o === '%' && isId(v1.a[0], t0.n) && isId(v1.a[1], bn)) an = t0.n;
    } else if (stmts.length === 3) {
      const [s1, s2, s3] = stmts;
      const asg = (st) => (st.s === 'decl' ? { t: { t: 'id', n: st.n }, v: st.init } : st.s === 'assign' && st.op === '=' ? { t: st.target, v: st.v } : st.s === 'expr' && st.e.t === 'assign' && st.e.op === '=' ? { t: st.e.target, v: st.e.v } : null);
      const [x1, x2, x3] = [asg(s1), asg(s2), asg(s3)];
      if (x1 && x2 && x3 && isId(x1.v, bn) && isId(x2.t, bn) && x2.v.t === 'op' && x2.v.o === '%' && isId(x2.v.a[0]) && isId(x2.v.a[1], bn) && isId(x3.t, x2.v.a[0].n) && isId(x3.v, x1.t.n)) an = x2.v.a[0].n;
    }
    if (!an) return null;
    const ra = env.get(an), rb = env.get(bn);
    if (!ra || !rb) return null;
    const v = A.add(this.initMag(ra, line), this.initMag(rb, line));
    return { trips: A.add(A.logE(v), ONE), why: `this is Euclid's algorithm: the remainder \`${an} % ${bn}\` is smaller than \`${bn}\` and the pair (a, b) → (b, a % b) at least halves \`a\` every two steps, so it runs O(log(${this.fmt(v).replace(/^O\(|\)$/g, '')})) times` };
  };

  /** cur = cur.next / cur.left / cur.right chains */
  P.pointerWalkPlan = function (s, env, line) {
    for (const c of conjuncts(s.cond)) {
      let name = null;
      if (c.t === 'id') name = c.n;
      else if (c.t === 'op' && (c.o === '!=' || c.o === '!==') && c.a[0].t === 'id' && c.a[1].t === 'null') name = c.a[0].n;
      else if (c.t === 'op' && c.o === '!=' && c.a[0].t === 'attr' && c.a[0].o.t === 'id' && c.a[1].t === 'null') name = c.a[0].o.n;
      else if (c.t === 'attr' && c.o.t === 'id') name = c.o.n;
      else if (c.t === 'op' && c.o === '!' && false) name = null;
      if (!name) continue;
      const rec = env.get(name);
      if (!rec || !(rec.ty.k === 'node' || rec.ty.k === 'tree' || rec.ty.k === 'nary')) continue;
      const ups = updatesOf(s.body, name);
      if (!ups.length) continue;
      const fields = new Set();
      // temporaries such as `nx = cur->next;` that are later assigned to the pointer
      const alias = new Map();
      eachStmt(s.body, (st) => { const a0 = st.s === 'decl' ? { target: { t: 'id', n: st.n }, op: '=', v: st.init } : asgOf(st); if (a0 && a0.op === '=' && a0.target.t === 'id' && a0.v && a0.v.t === 'attr') alias.set(a0.target.n, a0.v); });
      let ok = true;
      for (const u of ups) {
        const st = u.stmt;
        const a1 = asgOf(st);
        let v = a1 && a1.op === '=' && isId(a1.target, name) ? a1.v : null;
        if (v && v.t === 'id' && alias.has(v.n)) v = alias.get(v.n);
        let x = v, steps = 0;
        while (x && x.t === 'attr' && ['next', 'left', 'right', 'parent'].includes(x.n)) { fields.add(x.n); x = x.o; steps++; }
        if (!(a1 && a1.op === '=' && isId(a1.target, name) && x && isId(x, name) && steps >= 1)) ok = false;
      }
      if (!ok) continue;
      if (fields.has('parent')) continue;
      if (!progressOnAll(s.body, (st) => { const a2 = asgOf(st); return stmtHasUpdate(st, name) || (a2 && isId(a2.target, name)); })) continue;
      const root = rec.nodesOf || rec;
      const treeLike = fields.has('left') || fields.has('right');
      const sym = this.nodeCountSym(root, treeLike, line);
      if (!sym) continue;
      return { trips: sym, why: treeLike ? `\`${name}\` always moves from a node to one of its children, so it goes down the tree one level per iteration: at most h iterations (h = height of the tree)` : `\`${name}\` moves to \`${name}.next\` every iteration, so it visits each node of the list at most once: at most ${this.fmt(sym).replace(/^O\(|\)$/g, '')} iterations` };
    }
    return null;
  };
  P.nodeCountSym = function (root, treeLike, line) {
    if (!root || !root.isParam) { if (root && root.nodesCount) return treeLike ? root.heightSym : root.nodesCount; throw new Und(`cannot tell how many nodes the structure behind \`${root ? root.name : '?'}\` has (it is not an input parameter)`, line); }
    if (treeLike) return this.pSym(`h:${root.name}`, 'h', `height of the tree \`${root.name}\``, 'h', 'height', root.name);
    return this.pSym(`nodes:${root.name}`, 'n', `number of nodes of \`${root.name}\``, 'n', 'nodes', root.name);
  };

  // ------------------------------------------------------------------ amortised monotone pointer (sliding window)
  P.monotonePointerPlan = function (s, env, line) {
    if (this.fr.loops.length === 0) return null;
    const cands = [];
    const bodyAssigned = assignedNames(s.body);
    for (const name of bodyAssigned) {
      const rec = env.get(name);
      if (!rec || rec.ownerFn !== this.fr.fnKey || rec.loopVar) continue;
      if (!(rec.ty.k === 'int' || rec.ty.k === 'unknown')) continue;
      const ups = updatesOf(s.body, name);
      if (!ups.length || ups.some((u) => u.kind !== 'add' || u.c < 1)) continue;
      cands.push({ name, rec });
    }
    for (const { name, rec } of cands) {
      if (!progressOnAll(s.body, (st) => stmtHasUpdate(st, name, ['add']))) continue;
      // the pointer must be declared outside the enclosing loop and never move backwards anywhere else
      if ((rec.depth || 0) >= this.fr.loops.length) continue;
      const fnBody = this.fr.fn.body;
      const all = updatesOf(fnBody, name).filter((u) => !(u.stmt.s === 'decl'));
      const resets = all.filter((u) => u.kind !== 'add' && !((u.kind === 'other') && u.stmt.s === 'assign' && this.isEarlyInit(u.stmt, name, rec)));
      if (resets.length) continue;
      if (all.some((u) => u.kind === 'add' && u.c < 0)) continue;
      // the pointer value is bounded by an index use or by a comparison in the loop condition
      const bound = this.pointerBound(s, name, env, line);
      if (!bound) continue;
      const scale = this.multUntil(rec.depth || 0);
      const trips = A.mul(scale, bound.total);
      return { trips, global: true, why: `\`${name}\` is declared outside the enclosing loop and only ever moves forward (never reset), so across ALL iterations of the enclosing loop this \`while\` can run at most as many times in total as \`${name}\` can advance: ${bound.why} → ≤ ${this.fmt(trips).replace(/^O\(|\)$/g, '')} in total (amortised)` };
    }
    return null;
  };
  P.isEarlyInit = function (st) {
    // `l = 0` / `l, r = 0, n - 1` executed once, outside every loop
    if (!this.fr.topStmts) { this.fr.topStmts = new Set(this.fr.fn.body); }
    if (!this.fr.topStmts.has(st)) return false;
    const a = asgOf(st);
    if (!a || a.op !== '=') return false;
    const v = st.s === 'assign' ? st.v : null;
    return v !== null && (num(v) !== null || (v.t === 'lit' && v.kind === 'tuple' && v.a.every((x) => true)));
  };
  /** how far can pointer `name` advance? uses `X[name]` accesses or `name < bound` in the condition */
  P.pointerBound = function (s, name, env, line) {
    for (const c of conjuncts(s.cond)) {
      const cm = cmpOf(c, name);
      if (cm && (cm.op === '<' || cm.op === '<=') && !idsIn(cm.bound).has(name)) { try { const b = this.mag(cm.bound, env, line); return { total: A.add(b, ONE), why: `the loop condition requires \`${name} ${cm.op} ${show(cm.bound)}\`` }; } catch (err) { if (!(err instanceof Und)) throw err; } }
    }
    let found = null;
    const scan = (e) => eachExpr(e, (x) => {
      if (found) return;
      if (x.t === 'idx' && x.i.t === 'id' && x.i.n === name && x.o.t === 'id') { try { found = { total: A.add(this.sizeOf(x.o, env, line), ONE), why: `\`${name}\` is used as an index into \`${x.o.n}\`, so it is always < len(${x.o.n})` }; } catch (err) { if (!(err instanceof Und)) throw err; } }
      if (x.t === 'call' && x.recv && x.recv.t === 'id' && ['charAt', 'at', 'get'].includes(x.m) && x.a[0] && x.a[0].t === 'id' && x.a[0].n === name) { try { found = { total: A.add(this.sizeOf(x.recv, env, line), ONE), why: `\`${name}\` is used as an index into \`${x.recv.n}\`, so it is always < len(${x.recv.n})` }; } catch (err) { if (!(err instanceof Und)) throw err; } }
    });
    scan(s.cond);
    eachStmtExprs(s.body, (e) => { if (!found) scan(e); });
    return found;
  };

  // ------------------------------------------------------------------ drain loops (queue / stack / heap)
  P.drainContainer = function (cond, env) {
    for (const c of conjuncts(cond)) {
      let q = null;
      if (c.t === 'id') q = c.n;
      else if (c.t === 'op' && c.o === '!' && c.a[0].t === 'call' && c.a[0].recv && c.a[0].recv.t === 'id' && ['empty', 'isEmpty'].includes(c.a[0].m)) q = c.a[0].recv.n;
      else if (c.t === 'op' && c.o === '>' && c.a[0].t === 'call' && c.a[0].recv && c.a[0].recv.t === 'id' && ['size', 'length'].includes(c.a[0].m) && num(c.a[1]) === 0) q = c.a[0].recv.n;
      else if (c.t === 'op' && c.o === '>' && c.a[0].t === 'call' && c.a[0].fn === 'len' && c.a[0].a[0] && c.a[0].a[0].t === 'id' && num(c.a[1]) === 0) q = c.a[0].a[0].n;
      else if (c.t === 'call' && c.recv && c.recv.t === 'id' && ['size', 'length'].includes(c.m)) q = c.recv.n;
      else if (c.t === 'op' && c.o === '!=' && c.a[0].t === 'call' && c.a[0].recv && c.a[0].recv.t === 'id' && ['size', 'length'].includes(c.a[0].m) && num(c.a[1]) === 0) q = c.a[0].recv.n;
      else if (c.t === 'op' && c.o === '>=' && c.a[0].t === 'call' && c.a[0].fn === 'len' && c.a[0].a[0] && c.a[0].a[0].t === 'id' && num(c.a[1]) === 1) q = c.a[0].a[0].n;
      if (q) { const rec = env.get(q); if (rec && ['stack', 'queue', 'deque', 'heap', 'list', 'str', 'sb'].includes(rec.ty.k)) return q; }
    }
    return null;
  };

  P.drainPlan = function (s, env, line) {
    const q = this.drainContainer(s.cond, env);
    if (!q) throw new Und('the loop condition is not a simple "container is not empty" test', line, 'soft');
    const rec = this.growthTarget(env.get(q));
    // the loop must remove at least one element in every iteration
    this.fr.sizeAlias = this.fr.sizeAlias || new Map();
    eachStmt(this.fr.fn.body, (st) => { const a0 = st.s === 'decl' ? { target: { t: 'id', n: st.n }, v: st.init, op: '=' } : asgOf(st); if (a0 && a0.op === '=' && a0.target.t === 'id' && a0.v && ((a0.v.t === 'call' && a0.v.recv && isId(a0.v.recv, q) && ['size', 'length'].includes(a0.v.m)) || (a0.v.t === 'call' && a0.v.fn === 'len' && a0.v.a[0] && isId(a0.v.a[0], q)))) this.fr.sizeAlias.set(a0.target.n, q); });
    const popsAll = progressOnAll(s.body, (st, where) => where === 'cond' ? false : stmtPops(st, q) || this.levelBatchPops(st, q, env));
    if (!popsAll) throw new Und(`not every path through the loop body removes an element from \`${q}\`, so it cannot be shown that the loop shrinks \`${q}\``, line);
    // nobody may reassign the container in the loop
    if (assignedNames(s.body).has(q)) throw new Und(`\`${q}\` is reassigned inside the loop`, line);
    const bound = this.sizeBound(rec);
    const distinctPushes = this.pushesDistinct(rec);
    const popped = this.poppedVars(s.body, q);
    const outer = (rec.depth || 0) < this.fr.loops.length && rec.ownerFn === this.fr.fnKey;
    if (outer) {
      const total = A.mul(this.multUntil(rec.depth || 0), bound);
      return {
        trips: total, global: true,
        why: `\`${q}\` is created outside the surrounding loop and every iteration of this loop removes at least one element of it, so over ALL executions of the surrounding loop together this loop can run at most as often as elements are ever put into \`${q}\` (${this.fmt(total).replace(/^O\(|\)$/g, '')} in total — amortised)`,
        setup: () => { this.fr.popVars = new Set(popped); if (distinctPushes) this.fr.distinct = new Set([...(this.fr.distinct || []), ...popped]); },
      };
    }
    return {
      trips: bound,
      why: `every iteration removes at least one element of \`${q}\`, so the loop runs at most as many times as elements are ever put into \`${q}\`: its starting size plus everything pushed = ${this.fmt(bound).replace(/^O\(|\)$/g, '')}${distinctPushes ? ' (each pushed item is new — guarded by a visited check — so items are processed once)' : ''}`,
      setup: () => { this.fr.popVars = new Set(popped); if (distinctPushes) { this.fr.distinct = new Set([...(this.fr.distinct || []), ...popped]); } },
    };
  };
  /** `for _ in range(len(q))` whose body pops: counts as popping at least once when the queue is non-empty */
  P.levelBatchPops = function (st, q) {
    if (st.s !== 'for') return false;
    const sizeCall = (e) => e && ((e.t === 'call' && e.fn === 'len' && e.a[0] && isId(e.a[0], q)) || (e.t === 'call' && e.recv && isId(e.recv, q) && ['size', 'length'].includes(e.m)));
    let hi = st.mode === 'range' ? st.hi : st.mode === 'c' && st.cond && st.cond.t === 'op' && st.cond.o === '<' ? st.cond.a[1] : null;
    if (hi && hi.t === 'id' && this.fr.sizeAlias && this.fr.sizeAlias.get(hi.n) === q) hi = { t: 'call', recv: { t: 'id', n: q }, m: 'size', a: [] };
    if (!hi || !sizeCall(hi) || (st.mode === 'range' && st.lo && num(st.lo) !== 0)) return false;
    return progressOnAll(st.body, (x) => stmtPops(x, q));
  };
  P.poppedVars = function (body, q) {
    const out = [];
    eachStmt(body, (st) => {
      if (!stmtPops(st, q)) return;
      if (st.s === 'decl') out.push(st.n);
      else if (st.s === 'assign') { const t = st.target; if (t.t === 'id') out.push(t.n); else if (t.t === 'tuple') t.a.forEach((x) => x.t === 'id' && out.push(x.n)); }
      else if (st.s === 'expr' && st.e.t === 'assign' && st.e.target.t === 'id') out.push(st.e.target.n);
    });
    // `u = q.front(); q.pop();`  -> the variable assigned from q.front()/top()/peek()
    eachStmt(body, (st) => {
      const e = st.s === 'decl' ? st.init : st.s === 'assign' ? st.v : null;
      const nm = st.s === 'decl' ? st.n : st.s === 'assign' && st.target.t === 'id' ? st.target.n : null;
      if (nm && e && e.t === 'call' && e.recv && isId(e.recv, q) && ['front', 'top', 'peek', 'peekFirst', 'getFirst', 'element'].includes(e.m)) out.push(nm);
    });
    return out;
  };
  /** true when every push into the container is guarded by a first-visit mark (or happens once, outside every loop) */
  P.pushesDistinct = function (rec) {
    const list = this.growthList(rec);
    if (!list.length) return true;
    return list.every((g) => g.distinct || g.once);
  };
}
