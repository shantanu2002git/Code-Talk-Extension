// Time cost of expressions: operators, library calls (documented per data structure), allocation.
import * as A from './algebra.js';
import { Und, show, eqE } from './util.js';
import { isContainer, MUTATORS, REMOVERS } from './core.js';

const { ONE } = A;
const SEQ = new Set(['list', 'array', 'linked']);
const HASH = new Set(['set', 'map']);
const TREEK = new Set(['sortedset', 'sortedmap']);
const QUEUEK = new Set(['stack', 'queue', 'deque']);
const O1_ANY = new Set(['size', 'length', 'len', 'empty', 'isEmpty', 'capacity', 'front', 'back', 'top', 'peek', 'peekFirst', 'peekLast', 'element', 'getFirst', 'getLast', 'begin', 'end', 'rbegin', 'rend', 'cbegin', 'cend', 'at', 'charAt', 'get', 'set', 'first', 'last', 'data', 'hashCode', 'getKey', 'getValue', 'getOrDefault', 'containsKey']);

export function installExprCost(C) {
  const P = C.prototype;
  const log = (e) => A.add(A.logE(e), ONE);

  P.ec = function (e, env) {
    if (!e) return ONE;
    const line = e.line || this.curLine;
    switch (e.t) {
      case 'num': case 'id': case 'null': case 'unk': return ONE;
      case 'lit': { let t = ONE; for (const x of e.a) t = A.add(t, this.ec(x, env)); return e.kind === 'str' ? ONE : t; }
      case 'attr': return A.add(this.ec(e.o, env), ONE);
      case 'tuple': { let t = ONE; for (const x of e.a) t = A.add(t, this.ec(x, env)); return t; }
      case 'lambda': return ONE;
      case 'idx': {
        let t = A.add(this.ec(e.o, env), this.ec(e.i, env));
        const rt = this.typeOf(e.o, env);
        if (TREEK.has(rt.k)) { t = A.add(t, log(this.sizeOf(e.o, env, line))); }
        else if (rt.k === 'linked' || (rt.k === 'deque' && this.lang === 'python' && !(e.i.t === 'num' || (e.i.t === 'op' && e.i.o === 'neg')))) t = A.add(t, this.sizeOf(e.o, env, line));
        return t;
      }
      case 'slice': {
        this.noteTemp(() => this.sizeOf(e, env, line), line, `the slice \`${show(e)}\` is a copy`);
        let t = A.add(this.ec(e.o, env), ONE);
        for (const x of [e.lo, e.hi, e.step]) if (x) t = A.add(t, this.ec(x, env));
        return A.add(t, this.sizeOf(e, env, line));
      }
      case 'op': return this.opCost(e, env, line);
      case 'incdec': { if (e.target.t === 'idx') this.noteElementWrite(e.target, null, env, line); return A.add(this.ec(e.target, env), ONE); }
      case 'assign': {
        if (e.target.t === 'idx') this.noteElementWrite(e.target, e.v, env, line);
        let t = A.add(this.ec(e.target, env), this.ec(e.v, env));
        t = A.add(t, this.assignCopyCost(e.target, e.v, env, line));
        if (e.op === '+=' && this.typeOf(e.target, env).k === 'str' && !this.cppStringAppend(e)) t = A.add(t, this.sizeOf(e.target, env, line));
        return t;
      }
      case 'new': return this.newCost(e, env, line);
      case 'comp': this.noteTemp(() => this.sizeOf(e, env, line), line, 'the comprehension builds a new collection'); return this.compCost(e, env, line);
      case 'call': return this.callCost(e, env, line);
      default: return ONE;
    }
  };

  /** temporary copies: they are auxiliary memory while the statement runs */
  P.noteTemp = function (sizeFn, line, what) {
    if (!this.fr) return;
    let sz; try { sz = sizeFn(); } catch (err) { if (err instanceof Und) { (this.fr.tempErr = this.fr.tempErr || err); return; } throw err; }
    (this.fr.temps = this.fr.temps || []).push({ size: sz, line, what });
  };
  P.rootVarRec = function (e, env) { const r = this.rootVar(e); return r ? env.get(r.n) : null; };
  /** clearing a container costs its size, but each element is cleared once: charge the starting size once, the rest is covered by the pushes */
  P.pushGlobalSize = function (rec, line) {
    if (!rec || !rec.init || A.isOne(rec.init)) return;
    this.pushGlobal(rec.init, line, 'clearing the starting contents');
  };
  P.cppStringAppend = function () { return this.lang === 'cpp'; }; // std::string += is an in-place append (amortised O(1))
  P.pyStrConcatNote = function () { this.assume('String concatenation with `+` / `+=` is charged as copying the whole string (the language does not guarantee in-place appends).'); };

  /** C++ value semantics: `vector<int> a = b;` copies b. Other languages share references. */
  P.assignCopyCost = function (target, value, env, line) {
    if (this.lang !== 'cpp') return ONE;
    const vt = this.typeOf(value, env);
    if (!isContainer(vt) || vt.k === 'str' && false) return ONE;
    if (value.t === 'id' || value.t === 'idx' || value.t === 'attr') { try { return this.sizeOf(value, env, line); } catch (err) { if (err instanceof Und) throw err; throw err; } }
    return ONE; // temporaries are moved
  };

  P.opCost = function (e, env, line) {
    let t = ONE;
    for (const x of e.a) t = A.add(t, this.ec(x, env));
    const [a, b] = e.a;
    switch (e.o) {
      case '+': {
        const ta = this.typeOf(a, env), tb = this.typeOf(b, env);
        if (ta.k === 'str' || tb.k === 'str' || ta.k === 'list' || tb.k === 'list') {
          if (ta.k === 'str' || tb.k === 'str') this.pyStrConcatNote();
          const sa = ta.k === 'str' || ta.k === 'list' ? this.sizeOf(a, env, line) : ONE;
          const sb = tb.k === 'str' || tb.k === 'list' ? this.sizeOf(b, env, line) : ONE;
          t = A.add(t, A.add(sa, sb));
        }
        return t;
      }
      case '*': {
        const ta = this.typeOf(a, env), tb = this.typeOf(b, env);
        if (ta.k === 'list' || ta.k === 'str' && a.t !== 'num') return A.add(t, this.sizeOf(e, env, line));
        if (tb.k === 'list' || tb.k === 'str' && b.t !== 'num') return A.add(t, this.sizeOf(e, env, line));
        return t;
      }
      case 'in': case 'notin': {
        const rt = this.typeOf(b, env);
        if (HASH.has(rt.k)) return t;
        if (TREEK.has(rt.k)) return A.add(t, log(this.sizeOf(b, env, line)));
        if (rt.k === 'str') { const ta = this.typeOf(a, env); return A.add(t, ta.k === 'str' && a.t !== 'num' ? A.mul(this.sizeOf(b, env, line), this.sizeOf(a, env, line)) : this.sizeOf(b, env, line)); }
        if (rt.k === 'list' || rt.k === 'array' || rt.k === 'linked' || rt.k === 'deque' || rt.k === 'tuple') return A.add(t, this.sizeOf(b, env, line));
        if (b.t === 'lit' && b.kind !== 'str') return A.add(t, ONE);
        if (b.t === 'call' && b.fn === 'range') return t;
        throw new Und(`cannot tell what \`${show(b)}\` is, so the cost of \`${show(e)}\` (a list scan is O(size), a set lookup O(1)) is unknown`, line, 'type');
      }
      case '==': case '!=': case '<': case '<=': case '>': case '>=': {
        const ta = this.typeOf(a, env), tb = this.typeOf(b, env);
        if (a.t === 'lit' || b.t === 'lit' || a.t === 'num' || b.t === 'num' || ta.ch || tb.ch) return t; // comparing with a literal stops after a constant number of characters
        if ((ta.k === 'str' || ta.k === 'list' || ta.k === 'array') && (tb.k === ta.k)) return A.add(t, this.sizeOf(a, env, line));
        return t;
      }
      case 'fstr': return t;
      default: return t;
    }
  };

  P.newCost = function (e, env, line) {
    let t = ONE;
    for (const x of e.a) t = A.add(t, this.ec(x, env));
    if (e.init) t = A.add(t, this.ec(e.init, env));
    const ty = e.ty || { k: 'unknown' };
    if (e.alloc) { // new int[n][m] / int a[n][m]
      let n = ONE; for (const x of e.a) n = A.mul(n, this.mag(x, env, line));
      return A.add(t, n);
    }
    if (isContainer(ty) || ty.k === 'unknown') {
      if (!e.a.length) return t;
      const a0 = e.a[0];
      const t0 = this.typeOf(a0, env);
      if (e.brace) return t;
      if (isContainer(t0)) return A.add(t, this.sizeOf(a0, env, line)); // copy constructor
      if (e.a.length >= 1 && (t0.k === 'int' || a0.t === 'num' || a0.t === 'op' || a0.t === 'id' || a0.t === 'call')) {
        const n = this.mag(a0, env, line);
        let per = ONE;
        if (e.a[1] && isContainer(this.typeOf(e.a[1], env))) per = A.add(per, this.sizeOf(e.a[1], env, line));
        return A.add(t, A.mul(n, per));
      }
    }
    return t;
  };

  P.compCost = function (e, env, line) {
    const inner = new env.constructor(env);
    let trips = ONE; let t = ONE;
    for (const g of e.gens) {
      t = A.add(t, this.ec(g.iter, inner));
      const n = this.iterTrips(g.iter, inner, line);
      trips = A.mul(trips, n);
      this.bindLoopVars(g.vars, g.iter, inner, n, line);
    }
    let per = this.ec(e.elt, inner);
    for (const c of e.conds) per = A.add(per, this.ec(c, inner));
    // building a list of containers copies / allocates them as well
    return A.add(t, A.mul(trips, per));
  };

  // ---------------------------------------------------------------- calls
  P.callCost = function (e, env, line) {
    let t = ONE;
    if (e.recv) t = A.add(t, this.ec(e.recv, env));
    for (const x of e.a) t = A.add(t, e.fn && e.fn === 'sorted' ? ONE : this.ec(x, env));
    // user-defined function / method
    const user = this.resolveCall(e, env);
    if (user) return A.add(t, this.callUser(user, e, env, line));
    if (e.recv) return A.add(t, this.methodCost(e, env, line));
    return A.add(t, this.fnCost(e, env, line));
  };

  /** cost of the key / comparator functions passed to sort-like calls (per comparison) */
  P.lambdaCost = function (arg, env) {
    if (!arg) return ONE;
    if (arg.t === 'lambda') { const inner = new env.constructor(env); let c = ONE; try { c = this.block(arg.body, inner); } catch (err) { if (err instanceof Und) throw err; throw err; } return c; }
    return ONE; // named comparator / method reference: O(1) assumed only for lambdas we can see
  };
  const keyArg = (e) => { const kw = e.kw || []; const i = kw.indexOf('key'); if (i >= 0) return e.a[e.a.length - kw.length + i]; return e.a.find((x) => x.t === 'lambda'); };

  P.methodCost = function (e, env, line) {
    const m = e.m;
    const rt = this.typeOf(e.recv, env);
    const k = rt.k;
    const sz = () => this.sizeOf(e.recv, env, line);
    const nargs = e.a.length;
    if (['copy', 'clone', 'toCharArray', 'split', 'substr', 'substring', 'toArray', 'subList', 'keys', 'values', 'items'].includes(m) && k !== 'unknown') this.noteTemp(() => this.sizeOf(e, env, line), line, `\`.${m}()\` makes a copy`);
    if (REMOVERS.has(m)) { const rt0 = this.rootVar(e.recv); const rv0 = rt0 && env.get(rt0.n); if (rv0) this.growthTarget(rv0).hasRemoval = true; }
    this.noteMutation(e, env, line);
    if (k === 'tuple') return ONE;
    if (k === 'list' || k === 'array') {
      if (['push_back', 'append', 'emplace_back', 'pop_back', 'size', 'length', 'len', 'empty', 'isEmpty', 'front', 'back', 'at', 'get', 'set', 'capacity', 'data', 'begin', 'end', 'rbegin', 'rend', 'getFirst', 'getLast', 'peek', 'top'].includes(m)) return ONE;
      if (m === 'add') return nargs >= 2 ? sz() : ONE;
      if (m === 'pop') return nargs === 0 || (e.a[0].t === 'op' && e.a[0].o === 'neg') ? ONE : sz();
      if (m === 'clear' && nargs === 0) { this.pushGlobalSize(this.rootVarRec(e.recv, env), line); return ONE; } // every element is destroyed once: paid for by the push that created it
      if (['remove', 'erase', 'insert', 'indexOf', 'lastIndexOf', 'contains', 'index', 'count', 'find', 'reverse', 'clear', 'copy', 'clone', 'resize', 'assign', 'fill', 'toString', 'removeAll', 'retainAll', 'containsAll', 'equals', 'removeIf', 'swap'].includes(m)) {
        if (m === 'swap') return ONE;
        if (m === 'erase' && nargs === 1 && e.a[0].t === 'op' && e.a[0].o === '-' && e.a[0].a[0].t === 'call' && ['end'].includes(e.a[0].a[0].m)) return ONE; // v.erase(v.end()-1)
        return sz();
      }
      if (['extend', 'addAll', 'insertAll'].includes(m)) return nargs ? this.sizeOf(e.a[nargs - 1], env, line) : ONE;
      if (m === 'sort') { const kf = keyArg(e) || e.a[0]; return A.mul(sz(), A.mul(A.add(log(sz()), ONE), this.lambdaCost(kf, env))); }
      if (m === 'subList') return sz();
      if (m === 'stream' || m === 'iterator' || m === 'listIterator') return ONE;
      if (m === 'toArray') return sz();
    }
    if (k === 'str') {
      if (['size', 'length', 'len', 'empty', 'isEmpty', 'charAt', 'at', 'front', 'back', 'c_str', 'data', 'begin', 'end', 'push_back', 'pop_back', 'hashCode', 'append', 'capacity'].includes(m)) { if (m === 'append' && nargs && this.typeOf(e.a[0], env).k === 'str') return this.sizeOf(e.a[0], env, line); return ONE; }
      if (['find', 'indexOf', 'contains', 'rfind', 'lastIndexOf', 'count', 'replace', 'replaceAll', 'startswith', 'startsWith', 'endswith', 'endsWith', 'compare', 'compareTo', 'equals', 'equalsIgnoreCase', 'index', 'split', 'join', 'strip', 'lstrip', 'rstrip', 'trim', 'lower', 'upper', 'toLowerCase', 'toUpperCase', 'substr', 'substring', 'toCharArray', 'chars', 'copy', 'clone', 'reverse', 'isdigit', 'isalpha', 'isalnum', 'find_first_of', 'concat', 'toString', 'format', 'matches', 'repeat', 'insert', 'erase', 'swap'].includes(m)) {
        let c = sz();
        const a0 = e.a[0];
        if (['find', 'indexOf', 'contains', 'rfind', 'lastIndexOf', 'count', 'index', 'replace', 'replaceAll', 'split'].includes(m) && a0 && this.typeOf(a0, env).k === 'str' && a0.t !== 'num') { const lit = a0.t === 'lit' && a0.kind === 'str' && a0.len <= 1; if (!lit) c = A.mul(c, this.sizeOf(a0, env, line)); }
        if (m === 'substr' || m === 'substring') { const s2 = this.sizeOf(e, env, line); c = s2; }
        if (m === 'repeat') c = this.sizeOf(e, env, line);
        return c;
      }
    }
    if (k === 'sb') {
      if (['length', 'charAt', 'setCharAt', 'isEmpty', 'size', 'push_back', 'back'].includes(m)) return ONE;
      if (m === 'append') { const a0 = e.a[0]; if (a0 && this.typeOf(a0, env).k === 'str' && a0.t !== 'num') return this.sizeOf(a0, env, line); return ONE; }
      return sz(); // toString, reverse, insert, deleteCharAt, indexOf, substring ...
    }
    if (HASH.has(k)) {
      if (['get', 'put', 'containsKey', 'contains', 'add', 'remove', 'erase', 'count', 'find', 'insert', 'emplace', 'at', 'getOrDefault', 'setdefault', 'pop', 'discard', 'size', 'empty', 'isEmpty', 'merge', 'putIfAbsent', 'computeIfAbsent', 'compute', 'containsValue_', 'begin', 'end', 'keySet', 'values', 'entrySet', 'keys', 'items', 'getKey', 'getValue', 'contains_', 'try_emplace', 'insert_or_assign', 'extract', 'equals', 'hashCode', 'push_back'].includes(m)) {
        if (m === 'merge' && nargs >= 1 && this.typeOf(e.a[0], env).k === 'map') return this.sizeOf(e.a[0], env, line);
        if (m === 'add' || m === 'put' || m === 'insert' || m === 'emplace') this.assume('Hash table operations (`set` / `dict` / `HashMap` / `unordered_map`) take O(1) on average (assumes a good hash function, no adversarial collisions).');
        return ONE;
      }
      if (['update', 'putAll', 'addAll', 'union', 'intersection', 'difference', 'issubset', 'removeAll', 'retainAll', 'containsAll'].includes(m)) return nargs ? this.sizeOf(e.a[0], env, line) : ONE;
      if (['clear', 'copy', 'clone', 'toString', 'containsValue', 'stream', 'toArray'].includes(m)) return sz();
    }
    if (TREEK.has(k)) {
      if (['get', 'put', 'containsKey', 'contains', 'add', 'remove', 'erase', 'count', 'find', 'insert', 'emplace', 'at', 'lower_bound', 'upper_bound', 'floor', 'ceiling', 'higher', 'lower', 'floorKey', 'ceilingKey', 'higherKey', 'lowerKey', 'floorEntry', 'ceilingEntry', 'firstKey', 'lastKey', 'first', 'last', 'pollFirst', 'pollLast', 'firstEntry', 'lastEntry', 'pollFirstEntry', 'pollLastEntry', 'getOrDefault', 'putIfAbsent', 'merge', 'computeIfAbsent', 'compute'].includes(m)) return log(sz());
      if (['size', 'empty', 'isEmpty', 'begin', 'end', 'rbegin', 'rend', 'keySet', 'values', 'entrySet', 'headMap', 'tailMap', 'subMap', 'headSet', 'tailSet', 'descendingMap', 'descendingSet', 'descendingKeySet', 'getKey', 'getValue'].includes(m)) return ONE;
      if (['clear', 'copy', 'clone', 'putAll', 'addAll', 'toString'].includes(m)) return sz();
    }
    if (QUEUEK.has(k)) {
      if (['push', 'pop', 'top', 'front', 'back', 'peek', 'poll', 'offer', 'add', 'addFirst', 'addLast', 'removeFirst', 'removeLast', 'pollFirst', 'pollLast', 'peekFirst', 'peekLast', 'push_back', 'push_front', 'pop_back', 'pop_front', 'appendleft', 'popleft', 'append', 'size', 'empty', 'isEmpty', 'element', 'getFirst', 'getLast', 'emplace', 'emplace_back', 'emplace_front', 'offerFirst', 'offerLast', 'at', 'begin', 'end', 'empty_', 'search_'].includes(m)) { if (m === 'add' && nargs === 2) return sz(); if (m === 'at' && this.lang === 'python') return sz(); return ONE; }
      if (m === 'remove') return nargs ? sz() : ONE;
      if (['contains', 'indexOf', 'clear', 'copy', 'clone', 'extend', 'addAll', 'search', 'count', 'reverse', 'index', 'toString', 'rotate'].includes(m)) return m === 'extend' || m === 'addAll' ? this.sizeOf(e.a[0], env, line) : sz();
    }
    if (k === 'heap') {
      if (['push', 'offer', 'add', 'pop', 'poll', 'emplace'].includes(m) || (m === 'remove' && nargs === 0)) return log(sz());
      if (['top', 'peek', 'size', 'empty', 'isEmpty', 'element'].includes(m)) return ONE;
      if (['contains', 'remove', 'clear', 'toString', 'addAll'].includes(m)) return m === 'addAll' ? A.mul(this.sizeOf(e.a[0], env, line), log(sz())) : sz();
    }
    if (k === 'linked') {
      if (['push_back', 'push_front', 'pop_back', 'pop_front', 'front', 'back', 'size', 'empty', 'isEmpty', 'addFirst', 'addLast', 'removeFirst', 'removeLast', 'getFirst', 'getLast', 'peek', 'poll', 'offer', 'push', 'pop', 'pollFirst', 'pollLast', 'peekFirst', 'peekLast', 'begin', 'end', 'emplace_back', 'emplace_front', 'add'].includes(m) && !(m === 'add' && nargs === 2)) return ONE;
      return sz(); // get(i), set(i), remove(i), contains, indexOf, insert ...
    }
    // unknown receiver type: allowed only for operations that cost the same on every candidate type
    if (k === 'unknown' || k === 'obj' || k === 'int' || k === 'float' || k === 'bool') {
      if (['append', 'push_back', 'add', 'push', 'popleft', 'appendleft', 'size', 'length', 'len', 'empty', 'isEmpty', 'put', 'getOrDefault', 'containsKey', 'get', 'peek', 'poll', 'offer', 'top', 'front', 'back', 'charAt', 'at', 'emplace_back', 'pop_back', 'setdefault', 'discard'].includes(m) && !(m === 'add' && nargs === 2)) return ONE;
      if (m === 'pop' && nargs === 0) return ONE;
    }
    throw new Und(`\`${show(e)}\`: the data structure of \`${show(e.recv)}\` is not known, so the cost of \`.${m}()\` cannot be stated`, line, 'type');
  };

  /** record that a container grows (needed to bound the size of local containers) */
  P.noteMutation = function (e, env, line) {
    const m = e.m;
    if (!(MUTATORS.has(m) || m === 'add')) return;
    const root = this.rootVar(e.recv);
    let v = root && env.get(root.n);
    if (!v) return;
    const direct = e.recv.t === 'id';
    if (direct) v = this.growthTarget(v);
    else if (v.aliasOf) v = this.growthTarget(v);
    let outer = ONE, total = ONE;
    const val = e.a[e.a.length - 1];
    if (['extend', 'addAll', 'putAll', 'update'].includes(m) && e.a.length) {
      try { outer = this.sizeOf(val, env, line); total = outer; } catch (err) { if (!(err instanceof Und)) throw err; throw new Und(`cannot bound how much \`${show(e.recv)}\` grows in \`${show(e)}\``, line); }
    } else if (e.a.length) {
      const vt = this.typeOf(val, env);
      if (isContainer(vt) && direct) { try { total = this.sizeOf(val, env, line); } catch (err) { if (err instanceof Und) throw new Und(`cannot bound the size of the container appended to \`${show(e.recv)}\` in \`${show(e)}\``, line); throw err; } }
    }
    if (!direct) {
      // graph[u].append(x): the outer container is unchanged (a dict gains at most one key), the elements add to the total
      const rt = this.typeOf(root, env);
      this.recordGrowth(v, ONE, total, line, this.pushFlags(val, e));
      return;
    }
    this.recordGrowth(v, outer, total, line, this.pushFlags(val, e));
  };
  /** is this push guarded by a first-visit mark on the same item, or executed once outside every loop? */
  P.pushFlags = function (val, call) {
    const regs = this.fr.regions || [];
    const ids = val ? this.idNames([val]) : [];
    const distinct = !!val && ids.length > 0 && regs.some((r) => ids.every((n) => r.names.has(n)));
    const once = this.fr.loops.length === 0 && !this.fr.rec && this.stack.length === 1;
    let treeChild = null;
    if (val && val.t === 'attr' && ['left', 'right', 'next'].includes(val.n) && val.o.t === 'id' && this.fr.popVars && this.fr.popVars.has(val.o.n)) {
      // a node is only ever pushed as the child of a node that was popped: every node is pushed at most once
      for (const [, r] of this.fr.envRef ? this.fr.envRef.vars : []) if (r.isParam && ['tree', 'node', 'nary'].includes(r.ty.k)) { treeChild = this.nodeSym(r.nodesOf || r, 'nodes', 0); break; }
    }
    return { distinct: distinct || !!treeChild, once, balanced: !!(call && call.bal), treeChild };
  };

  // ---------------------------------------------------------------- plain functions
  P.fnCost = function (e, env, line) {
    const f = e.fn;
    const a = e.a;
    const sz0 = () => this.sizeOf(a[0], env, line);
    const nm = f.replace(/^std::/, '');
    // container constructors / conversions: cost of copying the argument
    if (['list', 'set', 'tuple', 'frozenset', 'dict', 'sorted', 'reversed', 'deque', 'collections.deque', 'Counter', 'collections.Counter', 'bytes', 'bytearray'].includes(nm)) {
      if (!a.length) return ONE;
      if (nm === 'sorted' || a.length && this.typeOf(a[0], env).k !== 'int') this.noteTemp(() => sz0(), line, `\`${nm}(...)\` makes a new collection`);
      if (nm === 'sorted') { const kf = keyArg(e); const n = sz0(); return A.add(n, A.mul(n, A.mul(log(n), this.lambdaCost(kf, env)))); }
      if (nm === 'reversed') return ONE;
      return this.typeOf(a[0], env).k === 'int' ? this.mag(a[0], env, line) : sz0();
    }
    if (['defaultdict', 'collections.defaultdict', 'OrderedDict'].includes(nm)) return ONE;
    if (nm === 'str') return a.length && this.typeOf(a[0], env).k !== 'int' && this.typeOf(a[0], env).k !== 'unknown' ? sz0() : ONE;
    if (['len', 'sizeof', 'size', 'id', 'type', 'isinstance', 'hash', 'ord', 'chr', 'bool', 'float', 'int', 'abs', 'pow', 'sqrt', 'floor', 'ceil', 'round', 'fabs', 'labs', 'llabs', 'cbrt', 'exp', 'log', 'log2', 'log10', 'sin', 'cos', 'tan', 'atan2', 'fmod', 'hypot', 'swap', 'iter_swap', 'make_pair', 'make_tuple', 'tie', 'pair', 'tuple_', 'next', 'prev', 'advance', 'distance', 'move', 'forward', 'identity', 'isdigit', 'isalpha', 'isalnum', 'islower', 'isupper', 'tolower', 'toupper', 'isspace', 'print', 'printf', 'puts', 'putchar', 'cout', 'exit', 'assert', 'rand', 'max_', 'iter', 'enumerate', 'zip', 'range', 'map', 'filter', 'divmod', 'isnan', 'isinf', 'bit_length', 'popcount', '__builtin_popcount', '__builtin_clz', '__builtin_ctz', '__builtin_popcountll', 'Pair', 'new_', 'getcwd'].includes(nm)) return ONE;
    if (/^(Math|math|StrictMath)\./.test(nm) || nm === 'numeric_limits' || /^Character\./.test(nm) || /^Integer\.(MAX|MIN|valueOf|parseInt|compare|toString|toBinaryString|bitCount|signum|highestOneBit|numberOfTrailingZeros|numberOfLeadingZeros|reverse)/.test(nm) || /^Long\./.test(nm) || /^Double\./.test(nm) || /^Boolean\./.test(nm) || nm === 'Objects.hash' || nm === 'Objects.equals') { if (/Integer\.toBinaryString|Integer\.toString/.test(nm)) return ONE; return /^Math\.(floorMod|floorDiv|max|min|abs|pow|sqrt|ceil|floor|round|log|exp|random|signum|hypot|cbrt|toIntExact|addExact|multiplyExact|subtractExact|sin|cos|tan|atan|atan2|log10)$/.test(nm) || /^math\./.test(nm) || nm === 'numeric_limits' || /^Character|^Integer|^Long|^Double|^Boolean|^Objects/.test(nm) ? ONE : (() => { throw new Und(`no cost rule for \`${nm}\``, line); })(); }
    if (nm === 'gcd' || nm === 'math.gcd' || nm === '__gcd' || nm === 'lcm') { let r = ONE; for (const x of a) r = A.add(r, A.logE(this.mag(x, env, line))); return A.add(ONE, r); }
    if (nm === 'min' || nm === 'max' || nm === 'Math.min' || nm === 'Math.max') {
      if (a.length >= 2 && !(a.length === 2 && isContainer(this.typeOf(a[0], env)))) return ONE;
      if (a.length === 1) return sz0();
      return ONE;
    }
    if (nm === 'sum' || nm === 'any' || nm === 'all' || nm === 'accumulate' || nm === 'math.fsum' || nm === 'fsum') { if (!a.length) return ONE; if (a[0].t === 'comp') return this.ec(a[0], env); return this.iterCostOf(a[0], env, line); }
    if (nm === 'sort' || nm === 'stable_sort' || nm === 'partial_sort') return this.stdRangeCost(e, env, line, 'sort');
    if (['reverse', 'fill', 'iota', 'max_element', 'min_element', 'count', 'count_if', 'find', 'find_if', 'unique', 'rotate', 'nth_element', 'next_permutation', 'prev_permutation', 'accumulate_', 'equal', 'copy', 'remove', 'remove_if', 'replace', 'transform', 'for_each', 'any_of', 'all_of', 'none_of', 'adjacent_find', 'is_sorted', 'swap_ranges', 'minmax_element', 'lexicographical_compare', 'memset', 'memcpy', 'fill_n', 'generate'].includes(nm)) return this.stdRangeCost(e, env, line, 'linear');
    if (['lower_bound', 'upper_bound', 'binary_search', 'equal_range'].includes(nm)) return this.stdRangeCost(e, env, line, 'log');
    if (['make_heap', 'push_heap', 'pop_heap', 'sort_heap'].includes(nm)) return this.stdRangeCost(e, env, line, nm === 'make_heap' ? 'linear' : 'log');
    if (/^(Arrays|Collections)\./.test(nm)) return this.javaUtilCost(nm, e, env, line);
    if (/^heapq\./.test(nm) || ['heappush', 'heappop', 'heapify', 'heappushpop', 'heapreplace', 'nlargest', 'nsmallest'].includes(nm)) {
      const g = nm.replace(/^heapq\./, '');
      if (g === 'heapify') return sz0();
      if (g === 'nlargest' || g === 'nsmallest') { const n = this.sizeOf(a[1], env, line); return A.mul(n, A.add(A.logE(this.mag(a[0], env, line)), ONE)); }
      const hv = this.rootVar(a[0]); const rec = hv && env.get(hv.n);
      if (g === 'heappush') { if (rec) this.recordGrowth(this.growthTarget(rec), ONE, ONE, line, this.pushFlags(a[1])); }
      return A.add(log(sz0()), ONE);
    }
    if (/^bisect(\.|_)/.test(nm) || ['bisect_left', 'bisect_right', 'bisect', 'insort'].includes(nm)) return /insort/.test(nm) ? sz0() : A.add(log(sz0()), ONE);
    if (['to_string', 'str_', 'stoi', 'stol', 'stoll', 'stod', 'atoi', 'atol', 'strlen', 'String.valueOf', 'String.valueOf_', 'Integer.parseInt', 'Long.parseLong', 'Double.parseDouble', 'String.copyValueOf'].includes(nm)) return a.length && this.typeOf(a[0], env).k === 'str' ? sz0() : ONE;
    if (nm === 'String.join' || nm === 'join') { let n = ONE; for (const x of a) { const t = this.typeOf(x, env); if (isContainer(t)) n = A.add(n, this.sizeOf(x, env, line)); } return n; }
    if (nm === 'String.format' || nm === 'format') return ONE;
    if (['Arrays.asList', 'List.of', 'Set.of', 'Map.of', 'Collections.emptyList', 'Optional.of'].includes(nm)) return ONE;
    if (nm === 'itertools.permutations' || nm === 'itertools.combinations' || nm === 'permutations' || nm === 'combinations' || nm === 'product') throw new Und('generating permutations / combinations / products has a size that depends on the data (factorial / binomial growth) and is not modelled', line);
    throw new Und(`no cost rule for the call \`${show(e)}\``, line, 'unknown-call');
  };

  P.iterCostOf = function (it, env, line) { return A.add(this.iterTrips(it, env, line), ONE); };

  /** std::sort(v.begin(), v.end()) and friends: the container is read from the iterator arguments */
  P.stdRangeCost = function (e, env, line, kind) {
    const a = e.a;
    const rangeVar = (x) => { let y = x; while (y && y.t === 'op' && (y.o === '+' || y.o === '-')) y = y.a[0]; return y && y.t === 'call' && y.recv && ['begin', 'end', 'rbegin', 'rend', 'cbegin', 'cend'].includes(y.m) ? y.recv : (y && y.t === 'id' ? y : null); };
    const r = rangeVar(a[0]);
    let n;
    if (r) { n = this.sizeOf(r, env, line); } else throw new Und(`the range of \`${show(e)}\` is not a whole container`, line);
    const cmp = a.find((x) => x.t === 'lambda');
    const per = cmp ? this.lambdaCost(cmp, env) : ONE;
    if (kind === 'sort') return A.mul(n, A.mul(A.add(log(n), ONE), per));
    if (kind === 'log') return A.add(log(n), ONE);
    return A.mul(n, per);
  };

  P.javaUtilCost = function (nm, e, env, line) {
    const a = e.a;
    const n0 = () => this.sizeOf(a[0], env, line);
    switch (nm) {
      case 'Arrays.sort': case 'Collections.sort': { const cmp = a.find((x) => x.t === 'lambda'); const per = cmp ? this.lambdaCost(cmp, env) : ONE; let n = n0(); if (a.length >= 3 && this.typeOf(a[1], env).k === 'int') n = A.add(this.mag(a[2], env, line), this.mag(a[1], env, line)); return A.mul(n, A.mul(A.add(log(n), ONE), per)); }
      case 'Arrays.fill': return a.length >= 4 ? A.add(this.mag(a[2], env, line), this.mag(a[1], env, line)) : n0();
      case 'Arrays.copyOf': case 'Arrays.copyOfRange': return this.sizeOf(e, env, line);
      case 'Arrays.equals': case 'Arrays.hashCode': case 'Arrays.toString': case 'Collections.reverse': case 'Collections.max': case 'Collections.min': case 'Collections.shuffle': case 'Collections.frequency': case 'Arrays.stream': case 'Collections.unmodifiableList': case 'Collections.addAll': case 'Arrays.deepToString': return n0();
      case 'Arrays.binarySearch': case 'Collections.binarySearch': return A.add(log(n0()), ONE);
      case 'Collections.swap': case 'Collections.emptyList': case 'Collections.singletonList': return ONE;
      case 'Arrays.asList': return ONE;
      default: throw new Und(`no cost rule for \`${nm}\``, line);
    }
  };
}
