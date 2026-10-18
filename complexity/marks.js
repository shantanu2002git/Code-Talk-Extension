// "First-visit marks": `if v not in seen: seen.add(v); ...rest...` (or `if seen[v]: continue; seen[v] = true; ...`).
// The statements after the mark run at most once per distinct key, so their *total* number of executions is bounded by
// the number of distinct keys (the domain), not by the number of times the guard is reached.
import * as A from './algebra.js';
import { Und, eachExpr, eachStmt, eachStmtExprs, eqE, idsIn, show } from './util.js';
import { isContainer } from './core.js';
import { asgOf, conjuncts, num } from './loops.js';

const { ONE } = A;
const isId = (e, n) => e && e.t === 'id' && (n === undefined || e.n === n);
const ADD = new Set(['add', 'insert', 'emplace', 'put', 'emplace_hint', 'try_emplace']);
const RESET = new Set(['erase', 'remove', 'discard', 'pop', 'clear', 'popitem', 'pop_back', 'removeAll']);
const PUSH = new Set(['push', 'push_back', 'append', 'add', 'offer', 'addLast', 'addFirst', 'appendleft', 'push_front', 'emplace_back', 'emplace', 'offerLast', 'offerFirst']);

const litKey = (e) => (e && e.t === 'num' ? 'n' + e.v : e && e.t === 'lit' && e.kind === 'str' ? 's' + e.s : null);
const litTruthy = (e) => (e.t === 'num' ? e.v !== 0 : (e.s || '').length > 0);
const exits = (list) => list.length > 0 && ['continue', 'return', 'break', 'throw'].includes(list[list.length - 1].s);

/** `E` is `V[i]` / `V[i][j]`: returns {V, idx:[...]} */
function elemChain(e) {
  const idx = []; let x = e;
  while (x && x.t === 'idx') { idx.unshift(x.i); x = x.o; }
  return x && x.t === 'id' && idx.length ? { V: x.n, idx } : null;
}
/** a predicate on an element or a hash membership test */
function parseTest(c) {
  if (!c) return null;
  if (c.t === 'op' && (c.o === '!' || c.o === 'not')) { const p = parseTest(c.a[0]); return p ? neg(p) : null; }
  // membership
  if (c.t === 'op' && (c.o === 'in' || c.o === 'notin') && c.a[1].t === 'id') return { kind: 'hash', V: c.a[1].n, K: c.a[0], present: c.o === 'in' };
  if (c.t === 'call' && c.recv && c.recv.t === 'id' && ['count', 'contains', 'containsKey', 'has', 'exists'].includes(c.m) && c.a.length === 1) return { kind: 'hash', V: c.recv.n, K: c.a[0], present: true };
  if (c.t === 'op' && ['==', '!=', '>', '<', '>='].includes(c.o)) {
    const [a, b] = c.a;
    const z = num(b);
    if (a.t === 'call' && a.recv && a.recv.t === 'id' && a.m === 'count' && a.a.length === 1 && z === 0) { if (c.o === '==') return { kind: 'hash', V: a.recv.n, K: a.a[0], present: false }; if (c.o === '!=' || c.o === '>') return { kind: 'hash', V: a.recv.n, K: a.a[0], present: true }; }
    if (a.t === 'call' && a.recv && a.recv.t === 'id' && a.m === 'find' && b.t === 'call' && b.recv && eqE(b.recv, a.recv) && b.m === 'end') return { kind: 'hash', V: a.recv.n, K: a.a[0], present: c.o === '!=' };
    if (a.t === 'call' && a.recv && a.recv.t === 'id' && ['get', 'getOrDefault'].includes(a.m) && b.t === 'null') return { kind: 'hash', V: a.recv.n, K: a.a[0], present: c.o === '!=' };
    const ch = elemChain(a);
    if (ch && litKey(b) !== null && (c.o === '==' || c.o === '!=')) return { kind: 'elem', ...ch, op: c.o === '==' ? 'eq' : 'ne', lit: b };
  }
  const ch = elemChain(c);
  if (ch) return { kind: 'elem', ...ch, op: 'truthy', lit: null };
  return null;
}
function neg(p) {
  if (p.kind === 'hash') return { ...p, present: !p.present };
  return { ...p, op: p.op === 'eq' ? 'ne' : p.op === 'ne' ? 'eq' : p.op === 'truthy' ? 'falsy' : 'truthy' };
}
const sat = (p, lit) => (p.op === 'truthy' ? litTruthy(lit) : p.op === 'falsy' ? !litTruthy(lit) : p.op === 'eq' ? litKey(lit) === litKey(p.lit) : litKey(lit) !== litKey(p.lit));

function markOf(s) {
  if (s.s === 'expr' && s.e.t === 'call' && s.e.recv && s.e.recv.t === 'id' && ADD.has(s.e.m) && s.e.a.length >= 1) return { kind: 'hash', V: s.e.recv.n, K: s.e.a[0] };
  const a = asgOf(s);
  if (a && a.op === '=') {
    const ch = elemChain(a.target);
    if (ch && litKey(a.v) !== null) return { kind: 'elem', ...ch, lit: a.v, alsoHash: ch.idx.length === 1 };
  }
  return null;
}

export function installMarks(C) {
  const P = C.prototype;

  P.tagMarks = function (fn) {
    if (fn.__tagged) return; fn.__tagged = true;
    const writesTo = (V, except) => { const w = []; eachStmt(fn.body, (st) => { if (st === except) return; const a = asgOf(st); if (a && a.target.t === 'idx') { const ch = elemChain(a.target); if (ch && ch.V === V) w.push(a); } }); return w; };
    const resets = (V) => { let r = false; eachStmtExprs(fn.body, (e) => { if (e.t === 'call' && e.recv && isId(e.recv, V) && RESET.has(e.m)) r = true; }); eachStmt(fn.body, (st) => { if (st.s === 'del') { const ch = elemChain(st.target); if (ch && ch.V === V) r = true; } }); return r; };
    const walk = (stmts, parentIf) => {
      stmts.forEach((s, i) => {
        const m = markOf(s);
        if (m) {
          let ok = false;
          // then-form: the enclosing if proceeds only when the key is new
          if (parentIf) for (const c of conjuncts(parentIf.cond)) { const t = parseTest(c); if (t && this.testMatches(t, m, 'then')) ok = true; }
          // early-exit form: an earlier `if (seen) continue/return;`
          for (let j = 0; j < i && !ok; j++) { const p = stmts[j]; if (p.s === 'if' && !(p.else && p.else.length) && exits(p.then)) for (const d of conjuncts(p.cond, '||')) { const t = parseTest(d); if (t && this.testMatches(t, m, 'exit')) ok = true; } }
          if (ok) {
            let sound = !resets(m.V);
            if (sound && m.kind === 'elem') sound = writesTo(m.V, s).every((a) => litKey(a.v) === litKey(m.lit));
            if (sound) s.mark = m;
          }
        }
        if (s.s === 'if') { walk(s.then, s); walk(s.else || [], null); }
        else if (s.s === 'while' || s.s === 'for') walk(s.body, null);
        else if (s.s === 'try') { walk(s.body, null); s.handlers.forEach((h) => walk(h, null)); walk(s.fin, null); }
        else if (s.s === 'switch') s.cases.forEach((b) => walk(b, null));
      });
    };
    walk(fn.body, null);
  };
  /** does test `t` guard mark `m` (same container, same key, and the mark makes the test fail next time)? */
  P.testMatches = function (t, m, form) {
    if (m.kind === 'hash') return t.kind === 'hash' && t.V === m.V && eqE(t.K, m.K) && (form === 'then' ? !t.present : t.present);
    if (m.kind === 'elem') {
      if (t.kind === 'hash' && m.alsoHash && t.V === m.V && eqE(t.K, m.idx[0])) return form === 'then' ? !t.present : t.present; // dict[key] = True after `key not in dict`
      if (t.kind !== 'elem' || t.V !== m.V || t.idx.length !== m.idx.length || !t.idx.every((x, k) => eqE(x, m.idx[k]))) return false;
      const s = sat(t, m.lit);
      return form === 'then' ? !s : s;
    }
    return false;
  };

  /** upper bound on how many times the statements after mark `s` can run, or null */
  P.markDomain = function (s, env, rest, line) {
    const m = s.mark;
    const rec = env.get(m.V);
    if (!rec) return null;
    const ty = rec.ty || { k: 'unknown' };
    const isHash = m.kind === 'hash' || (m.alsoHash && (ty.k === 'map' || ty.k === 'set'));
    const V = { t: 'id', n: m.V };
    if (!isHash && m.kind === 'elem') {
      if (m.idx.length === 1) {
        const d = this.sizeOf(V, env, line);
        return { D: d, keys: this.idNames(m.idx), why: `each position of \`${m.V}\` can be marked only once (${this.fmt(d).replace(/^O\(|\)$/g, '')} positions)`, V: rec };
      }
      if (m.idx.length === 2) {
        const d = A.mul(this.sizeOf(V, env, line), this.sizeOf({ t: 'idx', o: V, i: { t: 'num', v: 0 } }, env, line));
        return { D: d, keys: this.idNames(m.idx), why: `each cell of \`${m.V}\` can be marked only once (${this.fmt(d).replace(/^O\(|\)$/g, '')} cells)`, V: rec };
      }
      return null;
    }
    // hash-based visited set: the key space is bounded by the container it is used to index
    const keyNames = this.idNames([m.kind === 'hash' ? m.K : m.idx[0]]);
    const ev = this.keyEvidence(keyNames, rest, env, line);
    if (!ev) return null;
    return { D: ev.D, keys: keyNames, why: `a key is only processed the first time it is seen, and every key is used to index \`${ev.G}\`, so there are at most ${this.fmt(ev.D).replace(/^O\(|\)$/g, '')} different keys`, V: rec, assume: ev.assume };
  };
  P.idNames = function (es) { const out = []; for (const e of es) eachExpr(e, (x) => { if (x.t === 'id') out.push(x.n); }); return out; };

  /** find `G[key]` / `G[r][c]` in the statements that follow the mark, or through the queue the key is pushed to */
  P.keyEvidence = function (keyNames, rest, env, line) {
    const found = this.indexUse(keyNames, rest, env, line);
    if (found) return found;
    // the key is pushed to a queue / stack whose popped items are then used as an index
    let q = null;
    eachStmtExprs(rest, (e) => { if (q || e.t !== 'call' || !e.recv || e.recv.t !== 'id' || !PUSH.has(e.m) || !e.a.length) return; const ids = this.idNames([e.a[e.a.length - 1]]); if (ids.length && ids.every((n) => keyNames.includes(n))) q = e.recv.n; });
    if (!q) return null;
    const popped = this.poppedVars(this.fr.fn.body, q);
    if (!popped.length) return null;
    return this.indexUse(popped, this.fr.fn.body, env, line);
  };
  P.indexUse = function (names, stmts, env, line) {
    let res = null;
    const asm = 'Every vertex / key that is looked up in the container is one of its valid indices / keys, so the number of distinct keys is at most the container\'s size.';
    eachStmtExprs(stmts, (e) => {
      if (res) return;
      if (e.t === 'idx' && e.i.t === 'id' && names.includes(e.i.n)) {
        if (e.o.t === 'id') { const r = env.get(e.o.n); if (r && isContainer(r.ty)) { res = { D: this.sizeOf(e.o, env, line), G: e.o.n, assume: asm }; return; } }
        if (e.o.t === 'idx' && e.o.o.t === 'id' && e.o.i.t === 'id' && names.includes(e.o.i.n)) { const r = env.get(e.o.o.n); if (r && isContainer(r.ty)) res = { D: A.mul(this.sizeOf(e.o.o, env, line), this.sizeOf(e.o, env, line)), G: e.o.o.n, assume: asm }; }
      }
      if (e.t === 'call' && e.recv && e.recv.t === 'id' && ['get', 'at', 'getOrDefault'].includes(e.m) && e.a[0] && e.a[0].t === 'id' && names.includes(e.a[0].n)) { const r = env.get(e.recv.n); if (r && isContainer(r.ty)) res = { D: this.sizeOf(e.recv, env, line), G: e.recv.n, assume: asm }; }
    });
    return res;
  };
}
