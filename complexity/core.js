// Core of the complexity analyzer: symbols, environments, magnitude / size evaluation and the cost of expressions.
// Rule of this module: every quantity is either derived by an explicit rule or the analysis throws `Und` (cannot determine).
import * as A from './algebra.js';
import { Und, eachExpr, eqE, show, idsIn } from './util.js';

const { ONE } = A;

export class Env {
  constructor(parent = null) { this.vars = new Map(); this.parent = parent; this.defs = new Map(); }
  get(n) { for (let e = this; e; e = e.parent) if (e.vars.has(n)) return e.vars.get(n); return null; }
  has(n) { return !!this.get(n); }
  set(n, rec) { this.vars.set(n, rec); return rec; }
  def(n) { for (let e = this; e; e = e.parent) if (e.defs.has(n)) return e.defs.get(n); return null; }
}

const CONTAINERS = new Set(['list', 'array', 'str', 'sb', 'set', 'map', 'sortedmap', 'sortedset', 'stack', 'queue', 'deque', 'heap', 'linked']);
export const isContainer = (t) => t && CONTAINERS.has(t.k);
const SIZE_NAMES = new Set(['len', 'size', 'length', 'count']);
const MUTATORS = new Set(['push_back', 'push', 'append', 'add', 'put', 'insert', 'emplace', 'emplace_back', 'emplace_front', 'push_front', 'appendleft', 'addFirst', 'addLast', 'offer', 'offerFirst', 'offerLast', 'extend', 'addAll', 'putAll', 'setdefault', 'update', 'heappush', 'appendleft']);
const REMOVERS = new Set(['pop', 'pop_back', 'pop_front', 'popleft', 'poll', 'pollFirst', 'pollLast', 'remove', 'erase', 'clear', 'discard', 'removeFirst', 'removeLast', 'poll', 'heappop', 'popitem', 'del']);
export { MUTATORS, REMOVERS, SIZE_NAMES };

export function installCore(C) {
  const P = C.prototype;

  // ---------------------------------------------------------------- symbols
  P.newSym = function (kind, desc, pref) {
    const pool = pref ? [pref] : ['n', 'm', 'k', 'p', 'q', 'r', 's', 't'];
    let name = null;
    for (const c of pool) if (!this.symNames.has(c)) { name = c; break; }
    if (!name) name = `${pool[0]}${this.symNames.size}`;
    this.symNames.add(name);
    const id = `${name}`;
    this.syms[id] = { id, name, kind, desc };
    return A.sym(id);
  };
  /** parameter symbols are memoised so that every analysis pass uses the same symbol for the same thing */
  P.pSym = function (key, kind, desc, pref, what, param) {
    if (this.psyms.has(key)) return this.psyms.get(key);
    const s = this.newSym(kind, desc, pref);
    this.psyms.set(key, s);
    if (param) this.paramSyms.push({ param, sym: s, what: what || kind });
    return s;
  };
  P.symName = function (id) { return (this.syms[id] && this.syms[id].name) || id; };
  P.fmt = function (e) { return A.fmt(e, (s) => this.symName(s)); };

  // ---------------------------------------------------------------- variables
  P.declare = function (env, name, rec) { return env.set(name, { name, ...rec }); };

  /** lazily give an unknown-typed parameter a size symbol (used as a container) */
  P.needSize = function (v, line) {
    if (v.size) { if (!v.init) v.init = v.size; return v.size; }
    if (v.ty && v.ty.k !== 'unknown' && !isContainer(v.ty)) throw new Und(`the size of \`${v.name}\` is not known`, line);
    if (!v.isParam) throw new Und(`the size of \`${v.name}\` cannot be bounded`, line);
    v.size = this.pSym(`len:${v.name}`, 'len', `length of \`${v.name}\``, null, 'length', v.name);
    v.init = v.size;
    return v.size;
  };
  P.needVal = function (v, line) {
    if (v.val) return v.val;
    if (v.ty && v.ty.k !== 'unknown' && v.ty.k !== 'int' && v.ty.k !== 'float' && v.ty.k !== 'bool') throw new Und(`the numeric value of \`${v.name}\` is not known`, line);
    if (!v.isParam) throw new Und(v.noVal || `the value of \`${v.name}\` cannot be bounded`, line);
    v.val = this.pSym(`val:${v.name}`, 'val', `value of \`${v.name}\``, /^[a-zA-Z]$/.test(v.name) ? v.name : null, 'value', v.name);
    return v.val;
  };

  // ---------------------------------------------------------------- types of expressions (only what the cost rules need)
  P.typeOf = function (e, env) {
    if (!e) return { k: 'unknown' };
    switch (e.t) {
      case 'id': { const v = env.get(e.n); return v ? v.ty || { k: 'unknown' } : { k: 'unknown' }; }
      case 'num': return { k: e.bool ? 'bool' : 'int' };
      case 'lit': return { k: e.kind === 'str' ? 'str' : e.kind === 'dict' ? 'map' : e.kind === 'set' ? 'set' : e.kind === 'tuple' ? 'tuple' : 'list', e: e.a[0] ? this.typeOf(e.a[0], env) : { k: 'unknown' } };
      case 'new': return e.ty && e.ty.k !== 'unknown' ? e.ty : { k: 'unknown' };
      case 'idx': { const t = this.typeOf(e.o, env); if (t.k === 'str') return { k: 'str', ch: true }; if (t.k === 'map' || t.k === 'sortedmap') return t.e || { k: 'unknown' }; if (t.k === 'list' || t.k === 'array' || t.k === 'deque') return t.e || { k: 'unknown' }; return { k: 'unknown' }; }
      case 'slice': return this.typeOf(e.o, env);
      case 'comp': return { k: e.kind === 'set' ? 'set' : e.kind === 'dict' ? 'map' : 'list', e: { k: 'unknown' } };
      case 'op': if (['+', '-', '*', '/', '//', '%', '<<', '>>', '&', '|', '^', '**'].includes(e.o)) { const a = this.typeOf(e.a[0], env); if (e.o === '+' && (a.k === 'str' || a.k === 'list')) return a; if (e.o === '*' && (a.k === 'list' || this.typeOf(e.a[1], env).k === 'list')) return a.k === 'list' ? a : this.typeOf(e.a[1], env); return a.k === 'float' ? a : { k: 'int' }; } return { k: 'bool' };
      case 'call': {
        const f = e.fn;
        if (f === 'len' || f === 'size') return { k: 'int' };
        if (f === 'sorted' || f === 'list' || f === 'reversed') return { k: 'list', e: { k: 'unknown' } };
        if (f === 'set') return { k: 'set', e: { k: 'unknown' } };
        if (f === 'dict' || f === 'defaultdict' || f === 'Counter') return { k: 'map', key: { k: 'unknown' }, e: { k: 'unknown' } };
        if (f === 'deque' || f === 'collections.deque') return { k: 'deque', e: { k: 'unknown' } };
        if (f === 'str') return { k: 'str' };
        if (f === 'range') return { k: 'list', e: { k: 'int' }, range: true };
        if (f === 'int' || f === 'abs' || f === 'ord' || f === 'min' || f === 'max' || f === 'sum') return { k: 'int' };
        if (e.m) { const rt = this.typeOf(e.recv, env); if (['substr', 'substring', 'strip', 'lower', 'upper', 'toLowerCase', 'toUpperCase', 'trim', 'replace'].includes(e.m) && rt.k === 'str') return { k: 'str' }; if (['size', 'length', 'count', 'indexOf', 'find'].includes(e.m)) return { k: 'int' }; if (['get', 'at', 'charAt', 'front', 'back', 'top', 'peek', 'pop', 'poll', 'getOrDefault'].includes(e.m) && rt.e) return rt.e; if (['copy', 'clone'].includes(e.m)) return rt; if (e.m === 'toString') return { k: 'str' }; if (e.m === 'toCharArray') return { k: 'array', e: { k: 'int' } }; if (e.m === 'split') return { k: 'list', e: { k: 'str' } }; if (['keys', 'values', 'items'].includes(e.m)) return { k: 'list', e: { k: 'unknown' } }; }
        return { k: 'unknown' };
      }
      default: return { k: 'unknown' };
    }
  };

  // ---------------------------------------------------------------- magnitude of integer expressions
  P.mag = function (e, env, line = null) {
    line = e && e.line || line;
    switch (e.t) {
      case 'num': return ONE;
      case 'null': return ONE;
      case 'id': {
        const v = env.get(e.n);
        if (!v) { if (/^(INT_MAX|INT_MIN|LLONG_MAX|LLONG_MIN|MAX_VALUE|MIN_VALUE|INF|inf|NULL|true|false|MOD|mod)$/.test(e.n) || /^[A-Z_0-9]+$/.test(e.n) || /::(max|min|MAX_VALUE|MIN_VALUE)/.test(e.n)) return ONE; throw new Und(`the value of \`${e.n}\` is not known`, line); }
        return this.needVal(v, line);
      }
      case 'op': {
        const a = e.a;
        switch (e.o) {
          case '+': case '-': return A.add(this.mag(a[0], env, line), this.mag(a[1], env, line));
          case '*': return A.mul(this.mag(a[0], env, line), this.mag(a[1], env, line));
          case '/': case '//': case '>>': return this.mag(a[0], env, line);
          case '%': return this.mag(a[1], env, line);
          case 'neg': return this.mag(a[0], env, line);
          case '?:': return A.add(this.mag(a[1], env, line), this.mag(a[2], env, line));
          case '**': if (a[1].t === 'num') return A.pow(this.mag(a[0], env, line), a[1].v); throw new Und('a power with a non-constant exponent', line);
          case '<<': if (a[1].t === 'num') return this.mag(a[0], env, line); throw new Und('a left shift by a variable amount', line);
          case '&': case '|': case '^': return A.add(this.mag(a[0], env, line), this.mag(a[1], env, line));
          default: throw new Und(`cannot bound the expression \`${show(e)}\``, line);
        }
      }
      case 'call': {
        const f = e.fn || e.m;
        if (e.recv && SIZE_NAMES.has(e.m) && !e.a.length) return this.sizeOf(e.recv, env, line);
        if (!e.recv && (e.fn === 'len' || e.fn === 'size') && e.a.length === 1) return this.sizeOf(e.a[0], env, line);
        if (['min', 'Math.min', 'std::min', 'fmin'].includes(f) && e.a.length === 2) {
          let x = null, y = null; try { x = this.mag(e.a[0], env, line); } catch (err) { if (!(err instanceof Und)) throw err; } try { y = this.mag(e.a[1], env, line); } catch (err) { if (!(err instanceof Und)) throw err; }
          if (!x && !y) throw new Und(`cannot bound the value of \`${show(e)}\``, line);
          if (!x) return y; if (!y) return x;
          return A.geq(x, y) ? y : x; // min(a, b) is at most each of them: take the smaller bound
        }
        if (['max', 'Math.max', 'std::max', 'fmax'].includes(f) && e.a.length === 2) return A.add(this.mag(e.a[0], env, line), this.mag(e.a[1], env, line));
        if (['abs', 'Math.abs', 'int', 'float', 'floor', 'ceil', 'Math.floor', 'Math.ceil', 'round', 'Math.round', 'long', 'double', 'labs', 'llabs', 'fabs'].includes(f) && e.a.length === 1) return this.mag(e.a[0], env, line);
        if (['sqrt', 'Math.sqrt', 'isqrt', 'math.isqrt', 'math.sqrt', 'std::sqrt'].includes(f) && e.a.length === 1) return A.sqrtE(this.mag(e.a[0], env, line)) || (() => { throw new Und('square root of a non-simple expression', line); })();
        if (['ord', 'chr', 'Character.getNumericValue', 'Integer.bitCount', 'bool', 'hash'].includes(f)) return ONE;
        if (['sum', 'Sum', 'accumulate'].includes(f) && e.a.length >= 1) return this.dataVal('sum', e.a[0], env, line);
        if (['max', 'min', 'Math.max', 'Math.min', 'max_element', 'min_element', '*max_element', 'Collections.max', 'Collections.min'].includes(f) && e.a.length === 1) return this.dataVal('max', e.a[0], env, line);
        throw new Und(`cannot bound the value of \`${show(e)}\``, line);
      }
      case 'attr': {
        if (e.n === 'length' || e.n === 'size') return this.sizeOf(e.o, env, line);
        throw new Und(`cannot bound \`${show(e)}\``, line);
      }
      case 'idx': throw new Und(`\`${show(e)}\` is a stored data value — its size depends on the data, not on the input length`, line, 'data-dependent');
      case 'incdec': return this.mag(e.target, env, line);
      case 'assign': return this.mag(e.v, env, line);
      default: throw new Und(`cannot bound \`${show(e)}\``, line);
    }
  };

  // ---------------------------------------------------------------- number of elements of a container expression
  P.sizeOf = function (e, env, line = null) {
    line = e && e.line || line;
    switch (e.t) {
      case 'id': {
        const v = env.get(e.n);
        if (!v) throw new Und(`the size of \`${e.n}\` is not known`, line);
        if (v.isParam) { this.needSize(v, line); return this.sizeBound(v); }
        if (v.init) return this.sizeBound(v);
        throw new Und(`the size of \`${v.name}\` cannot be bounded`, line);
      }
      case 'lit': return e.kind === 'str' ? ONE : ONE;
      case 'slice': {
        if (e.lo && e.hi) { try { return A.add(this.mag(e.hi, env, line), this.mag(e.lo, env, line)); } catch { /* fall through */ } }
        return this.sizeOf(e.o, env, line);
      }
      case 'idx': {
        if (this.typeOf(e.o, env).k === 'str') return ONE;
        // element of a nested container: inner size (only valid one level down)
        if (e.o.t === 'idx') throw new Und(`the size of \`${show(e)}\` is not known (its elements have no known length)`, line);
        const base = this.rootVar(e.o);
        const v = base && env.get(base.n);
        if (v && v.inner) return v.inner;
        if (v && v.isParam && v.ty && (v.ty.k === 'list' || v.ty.k === 'array') && v.ty.e && isContainer(v.ty.e)) { v.inner = this.pSym(`row:${v.name}`, 'len', `length of each row of \`${v.name}\``, null, 'row length', v.name); return v.inner; }
        if (v && v.ty && v.ty.k === 'map' && v.inner) return v.inner;
        throw new Und(`the size of \`${show(e)}\` is not known`, line);
      }
      case 'new': return this.newSize(e, env, line);
      case 'call': {
        const f = e.fn || e.m;
        if (e.recv) {
          if (['copy', 'clone', 'toCharArray', 'keys', 'values', 'items', 'entrySet', 'keySet', 'stream'].includes(e.m)) return this.sizeOf(e.recv, env, line);
          if (['substr', 'substring'].includes(e.m)) { if (e.a.length === 2 && e.m === 'substr') return this.mag(e.a[1], env, line); return this.sizeOf(e.recv, env, line); }
          if (e.m === 'split') return this.sizeOf(e.recv, env, line);
          if (['strip', 'lstrip', 'rstrip', 'trim', 'lower', 'upper', 'toLowerCase', 'toUpperCase', 'replace', 'reverse', 'toString'].includes(e.m)) return this.sizeOf(e.recv, env, line);
          if (['subList'].includes(e.m)) return this.sizeOf(e.recv, env, line);
        }
        if (['list', 'set', 'tuple', 'sorted', 'reversed', 'dict', 'str', 'frozenset', 'deque', 'collections.deque', 'copy.copy', 'copy.deepcopy', 'bytearray', 'to_string'].includes(f)) { if (!e.a.length) return ONE; if (f === 'str' && e.a[0] && this.typeOf(e.a[0], env).k === 'int') return ONE; return this.sizeOf(e.a[0], env, line); }
        if (f === 'range') { if (e.a.length === 1) return this.mag(e.a[0], env, line); return A.add(this.mag(e.a[0], env, line), this.mag(e.a[1], env, line)); }
        if (f === 'String.valueOf' || f === 'Arrays.copyOf' || f === 'Arrays.copyOfRange') return e.a.length > 1 ? A.add(this.mag(e.a[1], env, line), e.a[2] ? this.mag(e.a[2], env, line) : ONE) : this.sizeOf(e.a[0], env, line);
        if (['Arrays.asList', 'List.of', 'Set.of'].includes(f)) return ONE;
        throw new Und(`the size of the result of \`${show(e)}\` is not known`, line);
      }
      case 'op': {
        if (e.o === '+') return A.add(this.sizeOf(e.a[0], env, line), this.sizeOf(e.a[1], env, line));
        if (e.o === '*') { const li = this.typeOf(e.a[0], env).k === 'list' || e.a[0].t === 'lit'; return li ? A.mul(this.sizeOf(e.a[0], env, line), this.mag(e.a[1], env, line)) : A.mul(this.mag(e.a[0], env, line), this.sizeOf(e.a[1], env, line)); }
        if (e.o === '?:') return A.add(this.sizeOf(e.a[1], env, line), this.sizeOf(e.a[2], env, line));
        throw new Und(`the size of \`${show(e)}\` is not known`, line);
      }
      case 'comp': {
        let n = ONE;
        for (const g of e.gens) n = A.mul(n, this.iterTrips(g.iter, env, line));
        return n;
      }
      case 'attr': {
        const root = this.rootVar(e.o);
        const v = root && env.get(root.n);
        if (v && v.ty && (v.ty.k === 'tree' || v.ty.k === 'node' || v.ty.k === 'nary') && (e.n === 'children' || e.n === 'neighbors')) return A.sym('__deg');
        throw new Und(`the size of \`${show(e)}\` is not known`, line);
      }
      default: throw new Und(`the size of \`${show(e)}\` is not known`, line);
    }
  };

  P.rootVar = function (e) { while (e && (e.t === 'idx' || e.t === 'attr' || e.t === 'slice')) e = e.o; return e && e.t === 'id' ? e : null; };

  /** number of elements allocated by `new ...` / constructor calls */
  P.newSize = function (e, env, line) {
    const ty = e.ty || { k: 'unknown' };
    if (e.alloc) { // arrays: new T[n][m]
      if (!e.a.length) return e.init ? ONE : ONE;
      return this.mag(e.a[0], env, line);
    }
    if (e.a.length === 0) return ONE;
    const a0 = e.a[0];
    if (isContainer(ty) || ty.k === 'unknown') {
      const t0 = this.typeOf(a0, env);
      if (isContainer(t0) || (a0.t === 'call' && !['int'].includes(a0.fn))) { try { return this.sizeOf(a0, env, line); } catch (err) { if (!(err instanceof Und)) throw err; } }
      if (e.brace || e.a.length === 1 && a0.t === 'lit') return ONE;
      return this.mag(a0, env, line);
    }
    return ONE;
  };

  // ---------------------------------------------------------------- trips of an iterable (python-style iteration)
  P.iterTrips = function (it, env, line = null) {
    line = it.line || line;
    if (it.t === 'call' && !it.recv) {
      const f = it.fn;
      if (f === 'range') return this.sizeOf(it, env, line);
      if (['enumerate', 'reversed', 'iter', 'list', 'tuple', 'set', 'sorted', 'frozenset'].includes(f) && it.a.length >= 1) return this.iterTrips(it.a[0], env, line);
      if (f === 'zip') { let r = null; for (const x of it.a) { const t = this.iterTrips(x, env, line); r = r ? A.add(r, t) : t; } return r || ONE; }
      if (f === 'map' || f === 'filter') return this.iterTrips(it.a[it.a.length - 1], env, line);
    }
    if (it.t === 'call' && it.recv && ['items', 'keys', 'values', 'iterator', 'entrySet', 'keySet', 'stream', 'chars', 'toCharArray'].includes(it.m)) return this.sizeOf(it.recv, env, line);
    if (it.t === 'call' && it.recv && it.m === 'split') return this.sizeOf(it.recv, env, line);
    return this.sizeOf(it, env, line);
  };

  // ---------------------------------------------------------------- growth of containers (sizes of locals)
  // A local container can hold at most: its initial size + every element ever added. "Every element ever added" is
  // (number of times the adding statement runs) x (elements added each time). Statement execution counts are only
  // known after the loops are analysed, so the analysis runs in passes until the growth table stops changing.
  P.recordGrowth = function (v, outer, total, line, flags = {}) {
    let mult = this.multSince(v.ownerFn === this.fr.fnKey ? (v.depth || 0) : 0, v);
    let fnKey = v.ownerFn && v.ownerFn !== this.fr.fnKey ? this.fr.fnKey : null; // growth done by a nested / recursive helper
    if (flags.treeChild) { mult = flags.treeChild; fnKey = null; }
    if (flags.balanced) { // push ... recurse ... pop in the same block: at most one element per live frame
      mult = (this.depthPrev && this.depthPrev.get(this.fr.fnKey)) || ONE; fnKey = null;
    }
    const k = `${v.ownerFn}:${v.name}`;
    const list = this.growthNow.get(k) || [];
    list.push({ mult, outer, total, fnKey, line, distinct: !!flags.distinct, once: !!flags.once, balanced: !!flags.balanced });
    this.growthNow.set(k, list);
  };
  P.growthList = function (v) { const k = `${v.ownerFn}:${v.name}`; return this.growthPrev.get(k) || this.growthNow.get(k) || []; };
  P.multOf = function (g) { let m = g.mult; if (g.fnKey) { const c = this.callsPrev.get(g.fnKey); if (c) m = A.mul(m, c); } return m; };
  /** most elements the container can hold */
  P.sizeBound = function (v) {
    let total = v.init || ONE;
    for (const g of this.growthList(v)) total = A.add(total, A.mul(this.multOf(g), g.outer));
    return total;
  };
  /** most elements it can hold counting the elements of nested containers (graph[u].append(v) counts here) */
  P.totalBound = function (v) {
    let total = v.totalInit || (v.inner ? A.mul(v.init || ONE, v.inner) : v.init || ONE);
    for (const g of this.growthList(v)) total = A.add(total, A.mul(this.multOf(g), g.total));
    return total;
  };
}
