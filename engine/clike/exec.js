// Statement execution, expression evaluation and calls for the tracing interpreter.
import * as V from './values.js';
import { BudgetError, Env, BRK, CONT, Ret, NUMERIC, SEQ_NAMES } from './interp.js';

const {
  Dbl, Chr, Pair, Tup, Obj, UNINIT, Cell, ElemRef, FieldRef, StrIdxRef, FnRef, MapObj, SetObj, Seq, Iter, Lambda,
  StrBuilder, RuntimeError, Unsupported, ThrowSignal, equals, cloneVal, cloneObj, compare,
} = V;

const isRef = (x) => x instanceof Cell || x instanceof ElemRef || x instanceof FieldRef || x instanceof StrIdxRef;
class ObjRef { // `*p = other` for struct pointers: copies fields
  constructor(o) { this.o = o; }
  get() { return this.o; }
  set(x) { if (x instanceof Obj) for (const k of Object.keys(x.f)) this.o.f[k] = cloneVal(x.f[k]); }
}
const LVALUE_KINDS = new Set(['id', 'member', 'index', 'deref', 'paren']);

export function installExec(Interpreter) {
  const P = Interpreter.prototype;

  P.tick = function tick() {
    if (++this.ops > this.maxOps) throw new BudgetError('The program ran for too many operations — it probably contains an infinite loop (or the input is too large for the visualizer).', 'ops');
    if ((this.ops & 4095) === 0 && this.deadline && Date.now() > this.deadline) throw new BudgetError('The program took too long to run in the visualizer (possible infinite loop).', 'time');
  };

  P.warn = function warn(msg, line) {
    const key = `${line}:${msg}`;
    if (this.warned.has(key)) return;
    this.warned.add(key);
    if (this.warnings.length < 30) this.warnings.push({ line, message: msg });
    const last = this.steps[this.steps.length - 1];
    if (last && !last.warn && !this.quiet) last.warn = msg;
  };

  // ------------------------------------------------------------ statements
  P.execBlockIn = function execBlockIn(block, env) {
    const saved = this.env;
    this.env = env;
    try {
      for (const s of block.stmts) { const r = this.exec(s); if (r) return r; }
    } finally { this.env = saved; }
    return undefined;
  };

  P.execStmts = function execStmts(stmts) {
    for (const s of stmts) { const r = this.exec(s); if (r) return r; }
    return undefined;
  };

  P.exec = function exec(n) {
    this.tick();
    this.line = n.line;
    switch (n.k) {
      case 'block': {
        const saved = this.env;
        this.env = new Env(saved);
        try { return this.execStmts(n.stmts); } finally { this.env = saved; }
      }
      case 'empty': return undefined;
      case 'expr': this.step(n.line); this.evalExpr(n.expr); return undefined;
      case 'decl': this.step(n.line); this.execDecl(n); return undefined;
      case 'bind': this.step(n.line); this.execBind(n); return undefined;
      case 'if': {
        const st = this.step(n.line);
        const c = this.truthy(this.evalExpr(n.cond));
        if (st) { st.cond = c; }
        if (c) return this.execScoped(n.then);
        if (n.else) return this.execScoped(n.else);
        return undefined;
      }
      case 'while': {
        for (;;) {
          this.tick();
          const st = this.step(n.line);
          const c = this.truthy(this.evalExpr(n.cond));
          if (st) st.cond = c;
          if (!c) break;
          const r = this.execScoped(n.body);
          if (r) { if (r === BRK) break; if (r === CONT) continue; return r; }
        }
        return undefined;
      }
      case 'dowhile': {
        for (;;) {
          this.tick();
          const r = this.execScoped(n.body);
          if (r) { if (r === BRK) break; if (r !== CONT) return r; }
          const ln = n.cond.line || n.line;
          const st = this.step(ln);
          const c = this.truthy(this.evalExpr(n.cond));
          if (st) st.cond = c;
          if (!c) break;
        }
        return undefined;
      }
      case 'for': return this.execFor(n);
      case 'foreach': return this.execForeach(n);
      case 'switch': return this.execSwitch(n);
      case 'return': return this.execReturn(n);
      case 'break': this.step(n.line); return BRK;
      case 'continue': this.step(n.line); return CONT;
      case 'throw': {
        this.step(n.line);
        const v = n.expr ? this.evalExpr(n.expr) : null;
        throw new ThrowSignal(v, n.line);
      }
      case 'try': return this.execTry(n);
      case 'localClass': this.registerClass(n.cls, false); this.initStatics(n.cls); return undefined;
      case 'typedefStmt': if (n.item) { const its = Array.isArray(n.item) ? n.item : [n.item]; for (const it of its) if (it.k === 'typedef') this.aliases[it.name] = it.type; } return undefined;
      default: throw new Unsupported(`Statement type "${n.k}" is not supported`, n.line);
    }
  };

  /** run a statement in its own scope (loop / if bodies) */
  P.execScoped = function execScoped(s) {
    if (s.k === 'block') return this.exec(s);
    const saved = this.env;
    this.env = new Env(saved);
    try { return this.exec(s); } finally { this.env = saved; }
  };

  P.execDecl = function execDecl(n) {
    const lang = this.lang;
    for (const d of n.decls) {
      const ty = this.resolveType(d.type);
      this.line = d.line || n.line;
      if (lang === 'cpp' && ty.ref && d.init && d.init.k !== 'initlist' && d.init.k !== 'ctorcall') {
        const lv = this.evalLvOrTemp(d.init);
        this.env.vars.set(d.name, lv);
        continue;
      }
      if (lang === 'cpp' && ty.name === 'auto' && ty.ptr === 0 && !ty.ref && d.init && d.init.k === 'call') { /* value */ }
      let v = this.initVar(ty, d.init, true, d.line);
      if (v instanceof Lambda && !v.name) v.name = d.name;
      const cell = new Cell(v, ty);
      this.env.vars.set(d.name, cell);
    }
  };

  P.execBind = function execBind(n) {
    const src = this.evalExpr(n.init);
    const byRef = n.type.ref;
    const parts = src instanceof Pair ? [src.first, src.second] : src instanceof Tup ? src.items : Array.isArray(src) ? src : null;
    if (!parts) throw new RuntimeError('Structured binding needs a pair, tuple or array', n.line);
    n.names.forEach((nm, i) => {
      if (byRef && src instanceof Pair) this.env.vars.set(nm, new FieldRef(src, i === 0 ? 'first' : 'second'));
      else this.env.vars.set(nm, new Cell(cloneVal(parts[i]), null));
    });
  };

  P.execFor = function execFor(n) {
    const saved = this.env;
    this.env = new Env(saved);
    try {
      if (n.init) { this.line = n.line; if (n.init.k === 'decl') this.execDecl(n.init); else this.evalExpr(n.init.expr); }
      for (;;) {
        this.tick();
        const st = this.step(n.line);
        const c = n.cond ? this.truthy(this.evalExpr(n.cond)) : true;
        if (st) st.cond = c;
        if (!c) break;
        const r = this.execScoped(n.body);
        if (r) { if (r === BRK) break; if (r !== CONT) return r; }
        if (n.update) { this.line = n.line; this.evalExpr(n.update); }
      }
      return undefined;
    } finally { this.env = saved; }
  };

  P.iterItems = function iterItems(coll, line) {
    if (coll instanceof Ref0) coll = coll.get();
    if (Array.isArray(coll)) return { n: () => coll.length, at: (i) => ({ ref: new ElemRef(coll, i), v: coll[i] }) };
    if (typeof coll === 'string') return { n: () => coll.length, at: (i) => ({ v: Chr.of(coll.charCodeAt(i)) }) };
    if (coll instanceof MapObj) { const es = coll.entries(); return { n: () => es.length, at: (i) => ({ v: es[i], pair: es[i] }) }; }
    if (coll instanceof SetObj) { const ks = coll.keys(); return { n: () => ks.length, at: (i) => ({ v: ks[i] }) }; }
    if (coll instanceof Seq) { const a = coll.kind === 'pq' ? coll.a.slice() : coll.a; return { n: () => a.length, at: (i) => ({ ref: new ElemRef(a, i), v: a[i] }) }; }
    if (coll === null) throw new RuntimeError('NullPointerException: iterating over null', line);
    throw new Unsupported(`Cannot iterate over ${this.describe(coll)}`, line);
  };
  const Ref0 = class { get() { return null; } };

  P.execForeach = function execForeach(n) {
    let coll = this.evalExpr(n.coll);
    if (isRef(coll)) coll = coll.get();
    const it = this.iterItems(coll, n.line);
    const ty = this.resolveType(n.type);
    const saved = this.env;
    try {
      for (let i = 0; i < it.n(); i++) {
        this.tick();
        const e = it.at(i);
        this.env = new Env(saved);
        if (n.names) {
          const p = e.v;
          const parts = p instanceof Pair ? [p.first, p.second] : p instanceof Tup ? p.items : Array.isArray(p) ? p : [];
          n.names.forEach((nm, k) => {
            if (ty.ref && p instanceof Pair) this.env.vars.set(nm, new FieldRef(p, k === 0 ? 'first' : 'second'));
            else this.env.vars.set(nm, new Cell(cloneVal(parts[k]), null));
          });
        } else if (this.lang === 'cpp' && ty.ref && e.ref) this.env.vars.set(n.name, e.ref);
        else if (this.lang === 'cpp' && ty.ref && e.pair) this.env.vars.set(n.name, new Cell(e.pair, null));
        else {
          let v = e.v;
          if (this.lang === 'cpp') v = this.copyIfValue(v, ty);
          this.env.vars.set(n.name, new Cell(ty.name === 'auto' || ty.name === 'var' ? v : this.coerce(v, ty), ty.name === 'auto' || ty.name === 'var' ? null : ty));
        }
        this.step(n.line);
        const r = this.exec(n.body);
        if (r) { if (r === BRK) break; if (r !== CONT) return r; }
      }
      return undefined;
    } finally { this.env = saved; }
  };

  P.execSwitch = function execSwitch(n) {
    this.step(n.line);
    const d = this.evalExpr(n.disc);
    let hit = -1;
    for (let i = 0; i < n.cases.length && hit < 0; i++) {
      const c = n.cases[i];
      if (c.isDefault) continue;
      for (const t of c.tests) { const tv = this.evalCaseLabel(t); if (this.eq(d, tv)) { hit = i; break; } }
    }
    if (hit < 0) hit = n.cases.findIndex((c) => c.isDefault);
    if (hit < 0) return undefined;
    const saved = this.env;
    this.env = new Env(saved);
    try {
      for (let i = hit; i < n.cases.length; i++) {
        const c = n.cases[i];
        const r = this.execStmts(c.body);
        if (r) { if (r === BRK) return undefined; return r; }
        if (c.arrow) break;
      }
    } finally { this.env = saved; }
    return undefined;
  };

  P.evalCaseLabel = function evalCaseLabel(t) {
    if (t.k === 'id' && !this.env.lookup(t.name)) { // Java enum label: case RED
      for (const c of Object.values(this.classes)) if (c.kind === 'enum' && c.enumConsts && t.name in c.enumConsts) return c.enumConsts[t.name];
    }
    return this.evalExpr(t);
  };

  P.execReturn = function execReturn(n) {
    this.step(n.line);
    let v;
    let has = false;
    const fr = this.frame;
    if (n.expr) {
      const rt = fr.retType ? this.resolveType(fr.retType) : null;
      if (rt && rt.name !== 'void' && rt.name !== 'auto') {
        v = this.evalTyped(n.expr, rt);
        if (rt.ref && this.lang === 'cpp') v = this.evalExpr(n.expr);
      } else v = this.evalExpr(n.expr);
      has = true;
    }
    this.line = n.line;
    this.step(n.line, 'return', v, has);
    return new Ret(v);
  };

  P.excName = function excName(e) {
    if (e instanceof ThrowSignal) return e.value instanceof Obj ? e.value.cls.name : 'exception';
    return e.exc || (e.type || 'RuntimeError');
  };

  P.execTry = function execTry(n) {
    const savedFrame = this.frame, savedEnv = this.env, savedDepth = this.depth, savedQuiet = this.quiet;
    let result;
    let pending = null;
    try {
      result = this.exec(n.body);
    } catch (e) {
      if (e instanceof BudgetError || e instanceof Unsupported || (e instanceof RangeError)) throw e;
      if (!(e instanceof ThrowSignal) && !(e instanceof RuntimeError)) throw e;
      this.frame = savedFrame; this.env = savedEnv; this.depth = savedDepth; this.quiet = savedQuiet;
      const thrown = e instanceof ThrowSignal ? e.value : this.makeException(e.exc || (this.lang === 'java' ? this.javaExcFor(e) : 'runtime_error'), e.message);
      const isCppCrash = this.lang === 'cpp' && e instanceof RuntimeError && !e.catchable;
      if (isCppCrash) throw e;
      let handled = false;
      for (const c of n.catches) {
        if (this.catchMatches(c, thrown)) {
          handled = true;
          const env = new Env(this.env);
          if (c.name) env.vars.set(c.name, new Cell(thrown, null));
          const saved = this.env;
          this.env = env;
          try { result = this.execStmts(c.body.stmts); } catch (e2) { pending = e2; } finally { this.env = saved; }
          break;
        }
      }
      if (!handled) pending = e;
    }
    if (n.fin) {
      const r = this.exec(n.fin);
      if (r) return r;
    }
    if (pending) throw pending;
    return result;
  };

  P.javaExcFor = function javaExcFor(e) {
    const m = /^(\w+Exception)/.exec(e.message);
    return m ? m[1] : 'RuntimeException';
  };

  P.catchMatches = function catchMatches(c, thrown) {
    const name = thrown instanceof Obj ? thrown.cls.name : '';
    for (const t of c.types) {
      if (t.name === '...' || t.name === 'Throwable' || t.name === 'Exception' || t.name === 'exception') return true;
      if (t.name === name) return true;
      if (thrown instanceof Obj && this.isSubclass(thrown.cls, t.name)) return true;
      if (t.name === 'RuntimeException' && /Exception$/.test(name) && !/^(IOException|InterruptedException)$/.test(name)) return true;
      if (t.name === 'runtime_error' && /error/.test(name)) return true;
    }
    return false;
  };

  // ------------------------------------------------------------ operators
  const isInt32 = (x) => (x | 0) === x;

  P.binop = function binop(op, a, b) {
    if (typeof a === 'number' && typeof b === 'number') {
      switch (op) {
        case '+': { const r = a + b; if ((r | 0) === r) return r; return isInt32(a) && isInt32(b) ? r | 0 : r; }
        case '-': { const r = a - b; if ((r | 0) === r) return r; return isInt32(a) && isInt32(b) ? r | 0 : r; }
        case '*': { const r = a * b; if ((r | 0) === r) return r; return isInt32(a) && isInt32(b) ? Math.imul(a, b) : r; }
        case '/': if (b === 0) throw this.divZero(); return Math.trunc(a / b);
        case '%': if (b === 0) throw this.divZero(); return (a % b) + 0;
        case '<': return a < b;
        case '<=': return a <= b;
        case '>': return a > b;
        case '>=': return a >= b;
        case '==': return a === b;
        case '!=': return a !== b;
        case '&': return isInt32(a) && isInt32(b) ? a & b : Number(BigInt(a) & BigInt(b));
        case '|': return isInt32(a) && isInt32(b) ? a | b : Number(BigInt(a) | BigInt(b));
        case '^': return isInt32(a) && isInt32(b) ? a ^ b : Number(BigInt(a) ^ BigInt(b));
        case '<<': return a << b;
        case '>>': return a >> b;
        case '>>>': return (a >>> b) | 0;
        default: break;
      }
    }
    return this.slowBin(op, a, b);
  };

  P.divZero = function divZero() {
    const e = new RuntimeError(this.lang === 'java' ? 'ArithmeticException: / by zero' : 'Division by zero (this crashes a real C++ program with a floating point exception)', this.line);
    e.exc = 'ArithmeticException';
    return e;
  };

  P.concat = function concat(a, b) {
    if (this.lang === 'java') return this.str(a) + this.str(b);
    const sa = a instanceof Chr ? a.s : typeof a === 'string' ? a : null;
    const sb = b instanceof Chr ? b.s : typeof b === 'string' ? b : null;
    if (sa !== null && sb !== null) return sa + sb;
    // "abc" + 3 is pointer arithmetic in C++
    if (typeof a === 'string' && (typeof b === 'number')) return a.slice(b);
    throw new RuntimeError('Cannot add a string and a non-string value in C++', this.line);
  };

  P.numLoose = function numLoose(x) {
    if (typeof x === 'number' || typeof x === 'bigint') return x;
    if (x instanceof Chr) return x.c;
    if (x instanceof Dbl) return x.v;
    if (typeof x === 'boolean') return x ? 1 : 0;
    if (x === UNINIT) return 0;
    return undefined;
  };

  P.eq = function eq(a, b) {
    if (a === b) return true;
    const x = this.numLoose(a), y = this.numLoose(b);
    if (x !== undefined && y !== undefined) return x == y; // eslint-disable-line eqeqeq
    if (a === null || b === null) return false;
    if (a instanceof Iter && b instanceof Iter) return a.pos === b.pos && (a.coll === b.coll || (isRef(a.coll) && isRef(b.coll) && a.coll.get() === b.coll.get()));
    if (a instanceof Obj && this.lang === 'cpp') { const m = this.findMethod(a.cls, 'operator==', 1); if (m) return this.truthy(this.invoke(m, [b], a, this.line)); }
    if (a instanceof Obj && this.lang === 'java' && a.cls.enumName === undefined) return false;
    if (typeof a === 'object' && typeof b === 'object') return equals(a, b);
    if (isRef(a) && isRef(b)) return a === b || (a.get && b.get && a.get() === b.get() && a.constructor === b.constructor && a.arr === b.arr && a.i === b.i);
    return false;
  };

  P.cmpVals = function cmpVals(a, b) {
    if (a instanceof Obj) {
      let m = this.findMethod(a.cls, 'compareTo', 1) || this.findMethod(a.cls, 'compare', 1);
      if (m) return this.toInt(this.invoke(m, [b], a, this.line));
      m = this.findMethod(a.cls, 'operator<', 1);
      if (m) { if (this.truthy(this.invoke(m, [b], a, this.line))) return -1; return (b instanceof Obj && this.truthy(this.invoke(m, [a], b, this.line))) ? 1 : 0; }
      if (a.cls.enumName !== undefined) return a.f.ordinal - b.f.ordinal;
      throw new RuntimeError(`Cannot compare objects of ${a.cls.name} (define operator< or compareTo)`, this.line);
    }
    if (a instanceof Pair && b instanceof Pair) { const c = this.cmpVals(a.first, b.first); return c || this.cmpVals(a.second, b.second); }
    if (Array.isArray(a) && Array.isArray(b)) { const n = Math.min(a.length, b.length); for (let i = 0; i < n; i++) { const c = this.cmpVals(a[i], b[i]); if (c) return c; } return a.length - b.length; }
    if (a === null || b === null) return a === b ? 0 : (a === null ? -1 : 1);
    return compare(a, b);
  };

  P.slowBin = function slowBin(op, a, b) {
    if (a === UNINIT) { a = 0; }
    if (b === UNINIT) { b = 0; }
    if (op === '+' && (typeof a === 'string' || typeof b === 'string' || (this.lang === 'java' && (a === null || b === null) && false))) return this.concat(a, b);
    if (op === '==' ) return this.eq(a, b);
    if (op === '!=') return !this.eq(a, b);
    if (op === '<' || op === '<=' || op === '>' || op === '>=') {
      const x = this.numLoose(a), y = this.numLoose(b);
      let c;
      if (x !== undefined && y !== undefined) { switch (op) { case '<': return x < y; case '<=': return x <= y; case '>': return x > y; default: return x >= y; } }
      if (a instanceof Iter && b instanceof Iter) { c = a.pos - b.pos; } else c = this.cmpVals(a, b);
      switch (op) { case '<': return c < 0; case '<=': return c <= 0; case '>': return c > 0; default: return c >= 0; }
    }
    if (a instanceof Obj && this.lang === 'cpp') {
      const m = this.findMethod(a.cls, `operator${op}`, 1);
      if (m) return this.invoke(m, [b], a, this.line);
    }
    if (a instanceof Iter || (a !== null && typeof a === 'object' && !(a instanceof Dbl) && !(a instanceof Chr))) {
      if (a instanceof Iter && (op === '+' || op === '-')) {
        if (b instanceof Iter) return a.pos - b.pos;
        return new Iter(a.coll, a.pos + (a.rev ? -1 : 1) * (op === '+' ? 1 : -1) * this.toInt(b), a.keys, a.rev);
      }
      if (Array.isArray(a) && (op === '+' || op === '-')) return new Iter(a, op === '+' ? this.toInt(b) : -this.toInt(b));
      if (typeof a === 'boolean') { /* fallthrough below */ } else if (!(a instanceof Dbl) && !(a instanceof Chr)) throw new RuntimeError(`Operator ${op} cannot be applied to ${this.describe(a)}`, this.line);
    }
    if (typeof a === 'boolean' && typeof b === 'boolean' && (op === '&' || op === '|' || op === '^')) return op === '&' ? a && b : op === '|' ? a || b : a !== b;
    if (a instanceof Dbl || b instanceof Dbl) {
      const x = this.num(a), y = this.num(b);
      switch (op) {
        case '+': return new Dbl(x + y);
        case '-': return new Dbl(x - y);
        case '*': return new Dbl(x * y);
        case '/': return new Dbl(x / y);
        case '%': return new Dbl(x % y);
        default: throw new RuntimeError(`Operator ${op} cannot be applied to a floating point number`, this.line);
      }
    }
    if (typeof a === 'bigint' || typeof b === 'bigint') {
      const x = BigInt.asIntN(64, BigInt(this.toInt(a) === undefined ? 0 : (typeof a === 'bigint' ? a : this.toInt(a))));
      const y = BigInt.asIntN(64, BigInt(typeof b === 'bigint' ? b : this.toInt(b)));
      const w = (r) => BigInt.asIntN(64, r);
      switch (op) {
        case '+': return w(x + y);
        case '-': return w(x - y);
        case '*': return w(x * y);
        case '/': if (y === 0n) throw this.divZero(); return w(x / y);
        case '%': if (y === 0n) throw this.divZero(); return w(x % y);
        case '&': return w(x & y);
        case '|': return w(x | y);
        case '^': return w(x ^ y);
        case '<<': return w(x << (y & 63n));
        case '>>': return w(x >> (y & 63n));
        case '>>>': return w(BigInt.asUintN(64, x) >> (y & 63n));
        default: break;
      }
    }
    if (a instanceof Chr || b instanceof Chr || typeof a === 'boolean' || typeof b === 'boolean') return this.binop(op, this.toInt(a), this.toInt(b));
    if (a === null || b === null) throw new RuntimeError(this.lang === 'java' ? 'NullPointerException: a null value was used in an expression' : 'Null pointer used in an expression', this.line);
    throw new RuntimeError(`Operator ${op} cannot be applied to ${this.describe(a)} and ${this.describe(b)}`, this.line);
  };

  P.incr = function incr(v, d) {
    if (typeof v === 'number') return (v + d) | 0 === v + d ? v + d : (Math.abs(v) <= 2147483647 ? (v + d) | 0 : v + d);
    if (v === UNINIT) { return d; }
    if (typeof v === 'bigint') return BigInt.asIntN(64, v + BigInt(d));
    if (v instanceof Chr) return Chr.of(v.c + d);
    if (v instanceof Dbl) return new Dbl(v.v + d);
    if (v instanceof Iter) return new Iter(v.coll, v.pos + (v.rev ? -d : d), v.keys, v.rev);
    if (v === null) throw new RuntimeError('NullPointerException: ++ on null', this.line);
    throw new RuntimeError(`Cannot apply ++/-- to ${this.describe(v)}`, this.line);
  };

  // ------------------------------------------------------------ expressions
  P.evalExpr = function evalExpr(n) {
    this.tick();
    switch (n.k) {
      case 'num':
        switch (n.kind) {
          case 'double': return new Dbl(n.value);
          case 'long': return BigInt.asIntN(64, n.value);
          default: return Number(n.value);
        }
      case 'str': return n.value;
      case 'const': return n.v;
      case 'chr': return Chr.from(n.value);
      case 'bool': return n.value;
      case 'null': return null;
      case 'this': return this.frame.thisObj;
      case 'id': return this.evalId(n);
      case 'paren': return this.evalExpr(n.expr);
      case 'unary': return this.evalUnary(n);
      case 'preinc': case 'postinc': {
        this.line = n.line;
        const ref = this.evalLv(n.expr);
        let old = ref.get();
        if (old === UNINIT) { this.warn(`The variable "${n.expr.name || 'value'}" is used before it has been given a value`, n.line); old = 0; }
        const nv = this.incr(old, n.op === '++' ? 1 : -1);
        ref.set(nv);
        return n.k === 'preinc' ? ref.get() : old;
      }
      case 'deref': return this.derefValue(this.evalExpr(n.expr), n.line);
      case 'addr': {
        if (LVALUE_KINDS.has(n.expr.k)) { const ref = this.evalLv(n.expr); const v = ref.get(); if (v instanceof Obj) { v.addrTaken = true; return v; } return ref; }
        return this.evalExpr(n.expr);
      }
      case 'bin': return this.evalBin(n);
      case 'assign': return this.evalAssign(n);
      case 'cond': return this.truthy(this.evalExpr(n.cond)) ? this.evalExpr(n.a) : this.evalExpr(n.b);
      case 'comma': this.evalExpr(n.left); return this.evalExpr(n.right);
      case 'call': this.line = n.line; return this.evalCall(n);
      case 'index': this.line = n.line; return this.evalIndex(n);
      case 'member': this.line = n.line; return this.evalMember(n);
      case 'scope': this.line = n.line; return this.evalScope(n);
      case 'cast': { const v = this.evalExpr(n.expr); return this.castTo(v, this.resolveType(n.type), n.line); }
      case 'construct': { this.line = n.line; if (n.type.name === 'get' && n.type.args[0] && n.type.args[0].k === 'num') { const tv = this.evalExpr(n.args[0]); const k = Number(n.type.args[0].value); const t = this.autoDeref(tv, n.line); return t instanceof Pair ? (k ? t.second : t.first) : Array.isArray(t) ? t[k] : t.items[k]; } const args = n.args.map((a) => this.evalExpr(a)); return this.constructTyped(this.resolveType(n.type), args, n.brace, n.line); }
      case 'new': return this.evalNew(n);
      case 'newarr': return this.evalNewArr(n);
      case 'lambda': return this.makeLambda(n);
      case 'initlist': return this.evalAny(n);
      case 'sizeof': return this.evalSizeof(n);
      case 'instanceof': {
        const v = this.evalExpr(n.expr);
        const ok = this.instanceOf(v, this.resolveType(n.type));
        if (ok && n.bind) this.env.vars.set(n.bind, new Cell(v, null));
        return ok;
      }
      case 'delete': return null;
      case 'throwExpr': throw new ThrowSignal(n.expr ? this.evalExpr(n.expr) : null, n.line);
      case 'typeexpr': throw new Unsupported('Type used as a value', n.line);
      default: throw new Unsupported(`Expression type "${n.k}" is not supported`, n.line);
    }
  };

  P.instanceOf = function instanceOf(v, ty) {
    if (v === null) return false;
    const n = ty.name;
    if (v instanceof Obj) return this.isSubclass(v.cls, n) || n === 'Object';
    switch (n) {
      case 'Integer': return typeof v === 'number';
      case 'Long': return typeof v === 'bigint';
      case 'Double': return v instanceof Dbl;
      case 'Character': return v instanceof Chr;
      case 'Boolean': return typeof v === 'boolean';
      case 'string': return typeof v === 'string';
      case 'Object': return true;
      case 'List': case 'ArrayList': return Array.isArray(v);
      default: return false;
    }
  };

  P.castTo = function castTo(v, ty, line) {
    if (ty.ptr || ty.dims) return v;
    if (this.lang === 'java' && v === null) return v;
    if (NUMERIC.has(ty.name) || ty.name === 'string') {
      if (ty.name === 'bool') return this.truthy(v);
      if (v instanceof Obj || v === null) return v;
      return this.coerce(v, ty);
    }
    return v;
  };

  P.evalSizeof = function evalSizeof(n) {
    const sizeOfType = (t) => {
      t = this.resolveType(t);
      if (t.ptr) return 8;
      const base = { int: 4, uint: 4, long: 8, ulong: 8, double: 8, char: 1, uchar: 1, bool: 1, short: 2, string: 32, vector: 24 }[t.name];
      let s = base || (this.classes[t.name] ? this.classes[t.name].fields.filter((f) => f.k === 'field' && !f.static).reduce((a, f) => a + sizeOfType(f.type), 0) : 8);
      if (t.arr) for (const d of t.arr) s *= d ? this.toInt(this.evalExpr(d)) : 1;
      return s;
    };
    let node = n;
    if (n.type && !n.type.ptr && !n.type.args.length && !n.type.arr) {
      const nm = n.type.name; const t0 = this.frame.thisObj;
      if (this.env.lookup(nm) || (t0 && nm in t0.f) || this.hasStaticField(nm)) node = { k: 'sizeof', expr: { k: 'id', name: nm, line: n.line }, line: n.line };
    }
    if (node.type) return sizeOfType(node.type);
    const v = this.evalExpr(node.expr);
    const sz = (x) => {
      if (Array.isArray(x)) { const et = x.et; return x.length * (x.length && Array.isArray(x[0]) ? sz(x[0]) : et ? sizeOfType(et) : 4); }
      if (typeof x === 'bigint' || x instanceof Dbl) return 8;
      if (x instanceof Chr) return 1;
      if (typeof x === 'boolean') return 1;
      return 4;
    };
    return sz(v);
  };

  P.evalUnary = function evalUnary(n) {
    const v = this.evalExpr(n.expr);
    switch (n.op) {
      case '!': return !this.truthy(v);
      case '-': {
        if (typeof v === 'number') return (-v) | 0 === -v ? -v : (Math.abs(v) <= 2147483647 ? -v : -v);
        if (typeof v === 'bigint') return BigInt.asIntN(64, -v);
        if (v instanceof Dbl) return new Dbl(-v.v);
        if (v instanceof Obj) { const m = this.findMethod(v.cls, 'operator-', 0); if (m) return this.invoke(m, [], v, n.line); }
        return -this.toInt(v);
      }
      case '+': return v instanceof Chr ? v.c : v;
      case '~': return typeof v === 'bigint' ? BigInt.asIntN(64, ~v) : ~this.toInt(v);
      default: throw new Unsupported(`Operator ${n.op}`, n.line);
    }
  };

  P.evalBin = function evalBin(n) {
    const op = n.op;
    if (op === '&&') { const l = this.evalExpr(n.left); if (!this.truthy(l)) return false; return this.truthy(this.evalExpr(n.right)); }
    if (op === '||') { const l = this.evalExpr(n.left); if (this.truthy(l)) return true; return this.truthy(this.evalExpr(n.right)); }
    const a = this.evalExpr(n.left);
    const b = this.evalExpr(n.right);
    this.line = n.line;
    if (op === '<<' && a !== null && typeof a === 'object' && a.isStream) return this.streamOut(a, b, n.right);
    if (op === '>>' && a !== null && typeof a === 'object' && a.isStream) throw new Unsupported('Reading input with cin is not supported', n.line);
    if (op === '<=>') return this.cmpVals(a, b);
    return this.binop(op, a, b);
  };

  P.readVar = function readVar(ref, name, line) {
    const v = ref.get();
    if (v === UNINIT) { this.warn(`The variable "${name}" is used before it has been given a value (reads as 0 here; in real C++ it is garbage)`, line); return 0; }
    return v;
  };

  P.evalId = function evalId(n) {
    const name = n.name;
    let ref = this.env.lookup(name);
    if (ref !== null) {
      const v = ref.get();
      if (v === UNINIT) return this.readVar(ref, name, n.line);
      return v;
    }
    const fr = this.frame;
    const t = fr.thisObj;
    if (t && name in t.f) return t.f[name];
    for (let c = fr.cls || (t && t.cls); c; c = c.base ? this.classes[c.base.name] : null) {
      if (c.statics && name in c.statics) return c.statics[name];
      if (c.enumConsts && name in c.enumConsts) return c.enumConsts[name];
    }
    // outer classes' statics (Java nested classes)
    for (const c of Object.values(this.classes)) { if (c.statics && name in c.statics && c.staticInitDone) return c.statics[name]; }
    const k = this.constantValue(name);
    if (k !== undefined) return k;
    if (this.funcs[name]) return new FnRef((args) => this.invoke(this.pickOverload(this.funcs[name], args, n.line, name), args, null, n.line), name);
    { const cc = this.collectMethods(fr.cls || (t && t.cls) || (fr.fn && fr.fn.cls && this.classes[fr.fn.cls]) || null, name); if (cc.length) return new FnRef((args) => this.invoke(this.pickOverload(cc, args, n.line, name), args, cc[0].isStatic ? null : t, n.line), name); }
    if (this.builtinFreeExists(name)) return new FnRef((args) => this.callBuiltinValues(name, args, n.line), name);
    if (this.classes[name]) return { $class: this.classes[name] };
    throw new RuntimeError(`"${name}" is not defined${this.lang === 'cpp' ? '' : ' (cannot find symbol)'}`, n.line);
  };

  // lvalues -----------------------------------------------------
  P.evalLvOrTemp = function evalLvOrTemp(n) { return LVALUE_KINDS.has(n.k) || n.k === 'cond' ? this.evalLv(n) : new Cell(this.evalExpr(n), null); };

  P.evalLv = function evalLv(n) {
    switch (n.k) {
      case 'id': {
        const ref = this.env.lookup(n.name);
        if (ref) return ref;
        const t = this.frame.thisObj;
        if (t && n.name in t.f) return new FieldRef(t.f, n.name, t.types && t.types[n.name]);
        for (let c = this.frame.cls || (t && t.cls); c; c = c.base ? this.classes[c.base.name] : null) {
          if (c.statics && n.name in c.statics) return new FieldRef(c.statics, n.name, c.staticTypes[n.name]);
        }
        for (const c of Object.values(this.classes)) if (c.statics && n.name in c.statics && c.staticInitDone) return new FieldRef(c.statics, n.name, c.staticTypes[n.name]);
        throw new RuntimeError(`"${n.name}" is not defined`, n.line);
      }
      case 'paren': return this.evalLv(n.expr);
      case 'member': return this.memberRef(n);
      case 'index': return this.indexRef(n);
      case 'deref': {
        const v = this.evalExpr(n.expr);
        if (isRef(v)) return v;
        if (v instanceof Obj) return new ObjRef(v);
        if (v instanceof Iter) return this.iterRef(v, n.line);
        if (Array.isArray(v)) return new ElemRef(v, 0);
        throw new RuntimeError('Segmentation fault: dereferencing a null or invalid pointer', n.line);
      }
      case 'cond': return this.truthy(this.evalExpr(n.cond)) ? this.evalLv(n.a) : this.evalLv(n.b);
      case 'scope': { const v = this.evalExpr(n); return new Cell(v, null); }
      default: { const v = this.evalExpr(n); return v && v.isTie ? v : new Cell(v, null); }
    }
  };

  P.iterRef = function iterRef(it, line) {
    const c = it.coll;
    if (Array.isArray(c)) { if (it.pos < 0 || it.pos >= c.length) throw new RuntimeError('Iterator is out of range (dereferencing end() or an invalid iterator)', line); return new ElemRef(c, it.pos); }
    if (typeof c === 'object' && c !== null && 'get' in c && 'set' in c && typeof c.get() === 'string') { const s = c.get(); if (it.pos >= s.length) throw new RuntimeError('Iterator is out of range', line); return new StrIdxRef(c, it.pos); }
    if (it.keys) { if (it.pos < 0 || it.pos >= it.keys.length) throw new RuntimeError('Iterator is out of range (dereferencing end() or an invalid iterator)', line); const e = it.keys[it.pos]; return new Cell(e, null); }
    throw new RuntimeError('Cannot dereference this iterator', line);
  };

  P.derefValue = function derefValue(v, line) {
    if (isRef(v)) return v.get();
    if (v instanceof Iter) return this.iterRef(v, line).get();
    if (v instanceof Obj) return v;
    if (Array.isArray(v)) return v[0];
    if (v === null) throw new RuntimeError('Segmentation fault: dereferencing a null pointer', line);
    return v;
  };

  P.autoDeref = function autoDeref(v, line) {
    if (isRef(v)) return v.get();
    if (v instanceof Iter) return this.iterRef(v, line).get();
    return v;
  };

  P.nullAccess = function nullAccess(what, line) {
    return new RuntimeError(this.lang === 'java' ? `NullPointerException: ${what} on a null reference` : `Segmentation fault: ${what} through a null pointer`, line);
  };

  P.memberRef = function memberRef(n) {
    const line = n.line;
    if (n.obj.k === 'id' && !this.env.lookup(n.obj.name) && !(this.frame.thisObj && n.obj.name in this.frame.thisObj.f)) {
      const sr = this.staticRef(n.obj.name, n.name);
      if (sr) return sr;
    }
    let o = this.evalExpr(n.obj);
    o = this.autoDeref(o, line);
    if (o === null) throw this.nullAccess(`accessing field "${n.name}"`, line);
    if (o instanceof Obj) {
      if (n.name in o.f) return new FieldRef(o.f, n.name, o.types && o.types[n.name]);
      for (let c = o.cls; c; c = c.base ? this.classes[c.base.name] : null) if (c.statics && n.name in c.statics) return new FieldRef(c.statics, n.name, c.staticTypes[n.name]);
      throw new RuntimeError(`${o.cls.name} has no field "${n.name}"`, line);
    }
    if (o instanceof Pair && (n.name === 'first' || n.name === 'second')) return new FieldRef(o, n.name, null);
    if (o && o.$class && o.$class.statics && n.name in o.$class.statics) return new FieldRef(o.$class.statics, n.name, o.$class.staticTypes[n.name]);
    return new Cell(this.evalMemberOn(o, n), null);
  };

  P.staticRef = function staticRef(cname, field) {
    const c = this.classes[cname];
    if (c) { if (!c.staticInitDone) this.initStatics(c); for (let k = c; k; k = k.base ? this.classes[k.base.name] : null) if (k.statics && field in k.statics) return new FieldRef(k.statics, field, k.staticTypes[field]); }
    return null;
  };

  P.checkIndex = function checkIndex(i, len, line, what = 'array') {
    if (i < 0 || i >= len) {
      const e = new RuntimeError(this.lang === 'java' ? `ArrayIndexOutOfBoundsException: Index ${i} out of bounds for length ${len}` : `Index ${i} is out of range for a ${what} of size ${len} (in C++ this is undefined behaviour and may crash or read garbage)`, line);
      e.exc = 'ArrayIndexOutOfBoundsException'; e.catchable = true;
      throw e;
    }
  };

  P.indexRef = function indexRef(n) {
    const line = n.line;
    let base = this.evalExpr(n.obj);
    const iv = this.evalKey(n.index, base);
    base = this.autoDeref(base, line);
    if (Array.isArray(base)) {
      const i = typeof iv === 'number' ? iv : this.toInt(iv);
      if ((i < 0 || i >= base.length) && this.lang === 'cpp' && i >= -8 && i < base.length + 64) {
        this.warn(`Index ${i} is outside the array (size ${base.length}). This is undefined behaviour in C++ — the visualizer ignores the access, but a real run may corrupt memory or crash.`, line);
        return new Cell(base.et && base.et.name === 'char' ? Chr.of(0) : 0, null);
      }
      this.checkIndex(i, base.length, line, this.lang === 'cpp' ? 'vector/array' : 'array');
      return new ElemRef(base, i);
    }
    if (typeof base === 'string') {
      const baseRef = LVALUE_KINDS.has(n.obj.k) ? this.evalLv(n.obj) : new Cell(base, null);
      const i = this.toInt(iv);
      this.checkIndex(i, base.length, line, 'string');
      return new StrIdxRef(baseRef, i);
    }
    if (base instanceof MapObj) { const e = this.mapEntry(base, iv, true); return new FieldRef(e, 'second', base.vt); }
    if (base instanceof Iter) { const i = this.toInt(iv); return this.iterRef(new Iter(base.coll, base.pos + i, base.keys), line); }
    if (base instanceof Obj) { const m = this.findMethod(base.cls, 'operator[]', 1); if (m) { const r = this.invoke(m, [iv], base, line); return isRef(r) ? r : new Cell(r, null); } }
    if (base === null) throw this.nullAccess('indexing', line);
    throw new RuntimeError(`Cannot index into ${this.describe(base)}`, line);
  };

  P.evalKey = function evalKey(node, base) {
    if (node.k === 'initlist') { const m = this.autoDeref(base, node.line); if (m instanceof MapObj && m.kt) return this.evalInitList(node, m.kt); return this.evalAny(node); }
    return this.evalExpr(node);
  };

  P.evalIndex = function evalIndex(n) {
    const line = n.line;
    let base = this.evalExpr(n.obj);
    const iv = this.evalKey(n.index, base);
    if (Array.isArray(base) && typeof iv === 'number') {
      if (iv < 0 || iv >= base.length) {
        if (this.lang === 'cpp' && iv >= -8 && iv < base.length + 64) { this.warn(`Index ${iv} is outside the array (size ${base.length}). This is undefined behaviour in C++ — here it reads as 0, but a real run may read garbage or crash.`, line); return base.et && base.et.name === 'char' ? Chr.of(0) : base.et && base.et.name === 'bool' ? false : 0; }
        this.checkIndex(iv, base.length, line, this.lang === 'cpp' ? 'vector/array' : 'array');
      }
      const v = base[iv];
      if (v === UNINIT) { this.warn(`An array element is read before it was given a value (reads as 0; in real C++ it is garbage)`, line); return 0; }
      return v;
    }
    base = this.autoDeref(base, line);
    if (Array.isArray(base)) {
      const i = this.toInt(iv);
      this.checkIndex(i, base.length, line, 'array');
      const v = base[i];
      if (v === UNINIT) { this.warn('An array element is read before it was given a value', line); return 0; }
      return v;
    }
    if (typeof base === 'string') { const i = this.toInt(iv); if (i === base.length && this.lang === 'cpp') return Chr.of(0); this.checkIndex(i, base.length, line, 'string'); return Chr.of(base.charCodeAt(i)); }
    return this.indexRef(n).get();
  };

  P.evalMember = function evalMember(n) {
    const line = n.line;
    const name = n.name;
    if (n.obj.k === 'id' && !this.env.lookup(n.obj.name)) {
      const t = this.frame.thisObj;
      if (!(t && n.obj.name in t.f) && !this.hasStaticField(n.obj.name)) {
        const sv = this.staticMember(n.obj.name, name, line);
        if (sv !== undefined) return sv;
      }
    }
    let o = this.evalExpr(n.obj);
    o = this.autoDeref(o, line);
    return this.evalMemberOn(o, n);
  };

  P.hasStaticField = function hasStaticField(name) {
    for (const c of Object.values(this.classes)) if (c.staticInitDone && c.statics && name in c.statics) return true;
    return false;
  };

  P.evalMemberOn = function evalMemberOn(o, n) {
    const name = n.name, line = n.line;
    if (o === null) throw this.nullAccess(`accessing "${name}"`, line);
    if (o instanceof Obj) {
      if (name in o.f) { const v = o.f[name]; return v === UNINIT ? 0 : v; }
      for (let c = o.cls; c; c = c.base ? this.classes[c.base.name] : null) { if (c.statics && name in c.statics) return c.statics[name]; }
      if (o.cls.enumName !== undefined || o.enumName !== undefined) { if (name === 'name') return o.enumName; }
      throw new RuntimeError(`${o.cls.name} has no field "${name}"`, line);
    }
    if (o instanceof Pair) { if (name === 'first' || name === 'getKey') return o.first; if (name === 'second' || name === 'getValue') return o.second; }
    if (Array.isArray(o) && name === 'length') return o.length;
    if (o && o.isStream) return o;
    if (o && o.$class) { const c = o.$class; if (!c.staticInitDone) this.initStatics(c); if (c.statics && name in c.statics) return c.statics[name]; if (c.enumConsts && name in c.enumConsts) return c.enumConsts[name]; }
    throw new RuntimeError(`Cannot read "${name}" of ${this.describe(o)}`, line);
  };

  P.staticMember = function staticMember(cname, name, line) {
    const c = this.classes[cname];
    if (c) {
      if (!c.staticInitDone) this.initStatics(c);
      for (let k = c; k; k = k.base ? this.classes[k.base.name] : null) {
        if (k.statics && name in k.statics) return k.statics[name];
        if (k.enumConsts && name in k.enumConsts) return k.enumConsts[name];
      }
      if (c.inner) { const inn = c.inner.find((x) => x.name === name); if (inn) return { $class: inn }; }
      return undefined;
    }
    return this.builtinStatic(cname, name, line);
  };

  P.evalScope = function evalScope(n) {
    const l = n.left;
    if (l.k === 'id') {
      if (l.name === 'std') { const k = this.constantValue(n.name); if (k !== undefined) return k; if (this.builtinFreeExists(n.name)) return new FnRef((args) => this.callBuiltinValues(n.name, args, n.line), n.name); }
      const c = this.classes[l.name];
      if (c) {
        const sv = this.staticMember(l.name, n.name, n.line);
        if (sv !== undefined) return sv;
        const list = c.byName[n.name];
        if (list) return new FnRef((args) => this.invoke(this.pickOverload(list, args, n.line, n.name), args, list[0].isStatic ? null : this.frame.thisObj, n.line), n.name);
      }
      if (l.name === 'string' && n.name === 'npos') return -1;
      const bs = this.builtinStatic(l.name, n.name, n.line);
      if (bs !== undefined) return bs;
    }
    if (l.k === 'this') { const t = this.frame.thisObj; const list = this.collectMethods(t.cls, n.name); if (list.length) return new FnRef((args) => this.invoke(this.pickOverload(list, args, n.line, n.name), args, t, n.line), n.name); }
    if (l.k === 'id' && !this.classes[l.name] && this.isBuiltinStaticClass(l.name)) {
      return new FnRef((args) => {
        try { return this.callStaticBuiltin(l.name, n.name, { line: n.line, args: args.map((v) => ({ k: 'const', v })), callee: null }); } catch (e) {
          if (!(e instanceof RuntimeError) || !/not supported/.test(e.message)) throw e;
          return this.callMethod(args[0], n.name, args.slice(1), null, { line: n.line, args: args.slice(1).map((v) => ({ k: 'const', v })) });
        }
      }, n.name);
    }
    if (l.k === 'typeexpr') { const bs = this.builtinStatic(l.type.name, n.name, n.line, l.type); if (bs !== undefined) return bs; }
    throw new RuntimeError(`Cannot resolve "${n.name}" in this scope`, n.line);
  };

  // assignment -------------------------------------------------
  P.evalAssign = function evalAssign(n) {
    this.line = n.line;
    const ref = this.evalLv(n.target);
    if (n.op === '=') {
      let v;
      const cur = ref.get();
      if (n.value.k === 'initlist') v = this.initLike(n.value, cur, ref);
      else v = this.evalExpr(n.value);
      this.assignInto(ref, v);
      return ref.get();
    }
    let cur = ref.get();
    if (cur === UNINIT) { this.warn(`The variable "${n.target.name || 'value'}" is used before it has been given a value`, n.line); cur = 0; }
    const rhs = this.evalExpr(n.value);
    if (cur instanceof Obj && this.lang === 'cpp') { const m = this.findMethod(cur.cls, `operator${n.op}`, 1); if (m) { this.invoke(m, [rhs], cur, n.line); return cur; } }
    if (n.op === '+=' && cur instanceof StrBuilder) { cur.s += this.str(rhs); return cur; }
    if (n.op === '+=' && typeof cur === 'string' && this.lang === 'cpp' && (typeof rhs === 'number')) { ref.set(cur + String.fromCharCode(rhs & 0xFF)); return ref.get(); }
    const nv = this.binop(n.op.slice(0, -1), cur, rhs);
    ref.set(nv);
    return ref.get();
  };

  P.assignInto = function assignInto(ref, v) {
    if (this.lang === 'cpp' && v !== null && typeof v === 'object' && !isRef(v) && !(v instanceof Iter) && !(v instanceof Lambda) && !(v instanceof FnRef)) {
      const ty = ref.ty || (ref.arr && ref.arr.et) || null;
      if (v instanceof Obj) { if (ty && !ty.ptr && !ty.ref && !v.heap && !v.addrTaken) v = cloneObj(v); } else if (!(ty && (ty.ptr || ty.ref))) v = cloneVal(v);
    }
    ref.set(v);
  };

  P.initLike = function initLike(node, cur, ref) {
    const ty = ref && (ref.ty || (ref.arr && ref.arr.et));
    if (ty && ty.k === 'type' && ty.name !== 'auto') return this.evalInitList(node, ty);
    if (cur instanceof Pair) return new Pair(this.evalExpr(node.items[0]), this.evalExpr(node.items[1]));
    if (cur instanceof Tup) return new Tup(node.items.map((x) => this.evalExpr(x)));
    if (Array.isArray(cur)) { const a = node.items.map((x) => cloneVal(cur.et ? this.evalTyped(x, cur.et) : this.evalAny(x))); if (cur.et) a.et = cur.et; return a; }
    if (cur instanceof Obj) return this.instantiate(cur.cls, node.items.map((x) => this.evalAny(x)), node.line);
    return this.evalAny(node);
  };

  // new -----------------------------------------------------------
  P.evalNew = function evalNew(n) {
    this.line = n.line;
    const args = n.args.map((a) => this.evalAny(a));
    const ty = this.resolveType(n.type);
    if (n.anon) {
      if (!this.classes[n.anon.name]) { this.registerClass(n.anon, false); }
      const o = this.instantiate(this.classes[n.anon.name], args, n.line);
      return o;
    }
    const v = this.constructTyped(ty, args, false, n.line);
    if (v instanceof Obj && this.lang === 'cpp') v.heap = true;
    return v;
  };

  P.evalNewArr = function evalNewArr(n) {
    const ty = this.resolveType(n.type);
    const dims = n.dims.map((d) => { const x = this.toInt(this.evalExpr(d)); if (x < 0) { const e = new RuntimeError(this.lang === 'java' ? `NegativeArraySizeException: ${x}` : 'Negative array size', n.line); e.exc = 'NegativeArraySizeException'; throw e; } if (x > 5_000_000) throw new RuntimeError('Array too large for the visualizer', n.line); return x; });
    if (n.init) return this.evalInitList(n.init, { ...ty, dims: (ty.dims || 0) + dims.length + n.extra });
    const base = { ...ty, dims: 0 };
    const elem = (k) => { // k = remaining dims
      const sz = dims[dims.length - k];
      const a = [];
      if (k === 1) {
        const et = n.extra ? { ...base, dims: n.extra, ptr: 0 } : base;
        a.et = et;
        for (let i = 0; i < sz; i++) a.push(n.extra ? null : this.defaultValue(base));
      } else {
        a.et = { ...base, dims: k - 1 + n.extra };
        for (let i = 0; i < sz; i++) a.push(elem(k - 1));
      }
      return a;
    };
    if (!dims.length) return [];
    return elem(dims.length);
  };

  // lambdas -------------------------------------------------------
  P.makeLambda = function makeLambda(n) {
    let env = this.env;
    const cap = n.captures || '&';
    if (this.lang === 'cpp' && !/^&?$/.test(cap) && !/^&,?/.test(cap) || (this.lang === 'cpp' && cap.startsWith('=')) ) {
      // copy-capture: = or explicit names
      const parts = cap.split(',').map((s) => s.trim()).filter(Boolean);
      const copyAll = parts.includes('=');
      const refAll = parts.includes('&');
      const capEnv = new Env(refAll ? this.env : this.genv);
      capEnv.isCapture = true;
      if (copyAll) {
        const chain = [];
        for (let e = this.env; e && !e.isGlobal; e = e.parent) { chain.unshift(e); if (e.fnRoot && !e.isLambda) break; }
        for (const e of chain) for (const [k, ref] of e.vars) capEnv.vars.set(k, new Cell(cloneVal(ref.get()), ref.ty || null));
      }
      for (const p of parts) {
        if (p === '=' || p === '&' || p === 'this') continue;
        if (p.startsWith('&')) { const ref = this.env.lookup(p.slice(1)); if (ref) capEnv.vars.set(p.slice(1), ref); } else { const nm = p.split('=')[0]; const ref = this.env.lookup(nm); if (ref) capEnv.vars.set(nm, new Cell(cloneVal(ref.get()), ref.ty || null)); }
      }
      env = capEnv;
    }
    return new Lambda(n, env, this.frame.thisObj, this.frame.cls);
  };

  P.callValue = function callValue(f, args, line = this.line) {
    if (isRef(f)) f = f.get();
    if (f instanceof Lambda) return this.callLambda(f, args, line);
    if (f instanceof FnRef) return f.call(args);
    if (f instanceof Obj) { const m = this.findMethod(f.cls, 'operator()', args.length) || this.functionalMethod(f, args.length); if (m) return this.invoke(m, args, f, line); }
    if (f === null) throw this.nullAccess('calling a function', line);
    throw new RuntimeError(`${this.describe(f)} is not callable`, line);
  };

  P.functionalMethod = function functionalMethod(o, argc) {
    for (const nm of ['apply', 'test', 'accept', 'get', 'compare', 'run', 'applyAsInt', 'call', 'applyAsLong', 'applyAsDouble']) { const m = this.findMethod(o.cls, nm, argc); if (m) return m; }
    return null;
  };

  P.callLambda = function callLambda(lam, args, line) {
    const n = lam.node;
    if (this.depth >= this.maxDepth) throw this.stackErr(line);
    const savedFrame = this.frame, savedEnv = this.env;
    const traced = !this.quiet;
    const fr = {
      fn: { name: lam.name || 'lambda' }, name: lam.name || 'lambda', fid: traced ? ++this.fidc : savedFrame.fid, pfid: traced ? savedFrame.fid : savedFrame.pfid,
      depth: savedFrame.depth + (traced ? 1 : 0), thisObj: lam.thisObj, cls: lam.frameInfo, retType: n.ret || null,
    };
    fr.env = new Env(lam.env, { fnRoot: true, isLambda: true });
    n.params.forEach((p, i) => {
      const ty = p.type ? this.resolveType(p.type) : null;
      let a = args[i];
      if (ty && ty.ref && this.lang === 'cpp') fr.env.vars.set(p.name, isRef(a) ? a : new Cell(a, ty));
      else {
        if (isRef(a) && !(ty && ty.ptr)) a = a.get();
        fr.env.vars.set(p.name, new Cell(ty ? this.coerce(a, ty) : a, ty));
      }
    });
    this.frame = fr; this.env = fr.env; this.depth++;
    const r = this.execStmts(n.body.stmts);
    let value;
    if (r instanceof Ret) value = r.v; else this.step(n.body.endLine, 'return');
    this.frame = savedFrame; this.env = savedEnv; this.depth--;
    if (n.ret && value !== undefined) value = this.coerce(value, this.resolveType(n.ret));
    return value;
  };

  P.stackErr = function stackErr(line) {
    const e = new RuntimeError(`Stack overflow: the recursion went deeper than ${this.maxDepth} calls (a real program would crash with a stack overflow if this recursion never stops; the visualizer also limits depth)`, line);
    e.exc = 'StackOverflowError'; e.stack_overflow = true;
    return e;
  };

  // ------------------------------------------------------------ calls
  P.prepareArgs = function prepareArgs(fn, argNodes) {
    const out = [];
    const params = fn.params;
    for (let i = 0; i < argNodes.length; i++) {
      const p = params[i] || params[params.length - 1];
      const node = argNodes[i];
      if (!p) { out.push(this.evalAny(node)); continue; }
      const ty = this.resolveType(p.type);
      if (p.type.varargs && i >= params.length - 1) { out.push(this.evalAny(node)); continue; }
      if (this.lang === 'cpp' && ty.ref) out.push(this.evalLvOrTemp(node.k === 'initlist' ? { k: 'cast', type: ty, expr: node } : node));
      else if (node.k === 'initlist') out.push(this.evalInitList(node, ty));
      else out.push(this.evalTyped(node, ty));
    }
    return out;
  };

  P.collectMethods = function collectMethods(cls, name) {
    const out = [];
    if (!cls) return out;
    for (let k = cls; k; k = k.base ? this.classes[k.base.name] : null) { const l = k.byName && k.byName[name]; if (l) for (const m of l) if (!out.some((o) => o.params.length === m.params.length && o.params.every((p, i) => p.type.name === m.params[i].type.name))) out.push(m); }
    return out;
  };

  P.evalCall = function evalCall(n) {
    const c = n.callee;
    const line = n.line;
    if (c.k === 'id') {
      const name = c.name;
      if (name === 'super') return this.callSuperCtor(n);
      const local = this.env.lookup(name);
      if (local) { const f = local.get(); return this.callValue(f, this.evalArgsLoose(n.args), line); }
      const fr = this.frame;
      const t = fr.thisObj;
      if (t && name in t.f && (t.f[name] instanceof Lambda || t.f[name] instanceof FnRef)) return this.callValue(t.f[name], this.evalArgsLoose(n.args), line);
      let cands = [];
      let target = null;
      if (t) { cands = this.collectMethods(t.cls, name); target = t; }
      if (!cands.length && fr.cls) { cands = this.collectMethods(fr.cls, name); if (cands.length && !cands[0].isStatic && !t) { /* instance call without this */ } }
      if (!cands.length && fr.fn && fr.fn.cls && this.classes[fr.fn.cls]) { cands = this.collectMethods(this.classes[fr.fn.cls], name); }
      if (!cands.length) {
        // inner / outer class method (Java nested)
        for (const k of Object.values(this.classes)) { if (k.prelude) continue; const l = k.byName[name]; if (l && l.every((m) => m.isStatic)) { cands = l; break; } }
      }
      if (!cands.length && this.funcs[name]) cands = this.funcs[name];
      if (cands.length) return this.callUser(cands, n.args, target, line, name);
      if (this.classes[name]) { const args = this.evalArgsLoose(n.args); const o = this.instantiate(this.classes[name], args, line); return o; }
      return this.callBuiltinNode(name, n);
    }
    if (c.k === 'this') { // this(...) constructor chaining
      const args = this.evalArgsLoose(n.args);
      const o = this.frame.thisObj;
      const ct = this.pickOverload(o.cls.ctors, args, line, o.cls.name);
      return this.invoke(ct, args, o, line, false, true);
    }
    if (c.k === 'scope') return this.callScope(n);
    if (c.k === 'member') return this.callMemberExpr(n);
    if (c.k === 'paren' || c.k === 'call' || c.k === 'index') { const f = this.evalExpr(c); return this.callValue(f, this.evalArgsLoose(n.args), line); }
    throw new Unsupported('This kind of call is not supported', line);
  };

  P.evalArgsLoose = function evalArgsLoose(argNodes) { return argNodes.map((a) => (a.k === 'initlist' ? this.evalAny(a) : this.copyArg(this.evalExpr(a)))); };

  P.copyArg = function copyArg(v) { return v; };

  P.callUser = function callUser(cands, argNodes, thisObj, line, name) {
    let fn;
    if (cands.length === 1) fn = cands[0];
    else {
      const sample = argNodes.map((a) => (a.k === 'initlist' ? null : this.evalExpr(a)));
      fn = this.pickOverload(cands, sample, line, name);
    }
    if (fn.params.length < argNodes.length && !(fn.params.length && fn.params[fn.params.length - 1].type.varargs)) throw new RuntimeError(`Too many arguments for "${name}"`, line);
    const args = this.prepareArgs(fn, argNodes);
    let recv = thisObj;
    if (fn.isStatic) recv = null;
    else if (thisObj && thisObj.cls !== undefined) { const real = this.collectMethods(thisObj.cls, name); if (real.length) { const same = real.find((m) => m.params.length === fn.params.length) || fn; fn = same; } }
    return this.invoke(fn, args, recv, line);
  };

  P.callSuperCtor = function callSuperCtor(n) {
    const o = this.frame.thisObj;
    const args = this.evalArgsLoose(n.args);
    const base = o.cls.base ? this.classes[o.cls.base.name] : null;
    if (!base) { // Exception subclasses
      if (args.length && typeof args[0] === 'string') o.f.message = args[0];
      return undefined;
    }
    this.construct(base, o, args, n.line);
    return undefined;
  };

  P.callScope = function callScope(n) {
    const c = n.callee;
    const l = c.left;
    const line = n.line;
    if (l.k === 'id') {
      const cls = this.classes[l.name];
      if (cls) {
        const cands = this.collectMethods(cls, c.name);
        if (cands.length) { const t = this.frame.thisObj; return this.callUser(cands, n.args, cands[0].isStatic ? null : t, line, c.name); }
        if (c.name === l.name) { return this.instantiate(cls, this.evalArgsLoose(n.args), line); }
      }
      if (l.name === 'std' || l.name === 'ranges') return this.callBuiltinNode(c.name, n);
      if (cls && cls.kind === 'enum' && ['values', 'valueOf'].includes(c.name)) return this.callStaticBuiltin(l.name, c.name, n);
      return this.callStaticBuiltin(l.name, c.name, n);
    }
    if (l.k === 'typeexpr') return this.callStaticBuiltin(l.type.name, c.name, n, l.type);
    throw new Unsupported('Unsupported scoped call', line);
  };

  P.callMemberExpr = function callMemberExpr(n) {
    const c = n.callee;
    const line = n.line;
    const name = c.name;
    const o = c.obj;
    if (o.k === 'id' && o.name === 'super') {
      const t = this.frame.thisObj;
      const base = t && t.cls.base ? this.classes[t.cls.base.name] : null;
      const cands = base ? this.collectMethods(base, name) : [];
      if (cands.length) return this.callUser(cands, n.args, t, line, name);
      return this.callObjectBuiltin(t, name, this.evalArgsLoose(n.args), line);
    }
    if (o.k === 'id' && !this.env.lookup(o.name)) {
      const t = this.frame.thisObj;
      const isField = t && o.name in t.f;
      if (!isField && !this.hasStaticField(o.name)) {
        const cls = this.classes[o.name];
        if (cls) {
          const cands = this.collectMethods(cls, name);
          if (cands.length) return this.callUser(cands, n.args, cands[0].isStatic ? null : this.frame.thisObj, line, name);
          return this.callStaticBuiltin(o.name, name, n);
        }
        if (this.isBuiltinStaticClass(o.name)) return this.callStaticBuiltin(o.name, name, n);
      }
    }
    // receiver (keep an lvalue reference for strings that are mutated in place)
    let ref = null;
    let recv;
    if (LVALUE_KINDS.has(o.k)) { ref = this.evalLv(o); recv = ref.get(); } else recv = this.evalExpr(o);
    if (recv === UNINIT) recv = 0;
    if (isRef(recv)) { ref = recv; recv = recv.get(); }
    if (recv instanceof Iter && !(name === 'hasNext' || name === 'next')) recv = this.derefValue(recv, line);
    if (recv === null) throw this.nullAccess(`calling "${name}()"`, line);
    if (recv instanceof Obj) {
      const cands = this.collectMethods(recv.cls, name);
      if (cands.length) return this.callUser(cands, n.args, recv, line, name);
      // field holding a lambda
      if (name in recv.f && (recv.f[name] instanceof Lambda || recv.f[name] instanceof FnRef)) return this.callValue(recv.f[name], this.evalArgsLoose(n.args), line);
      return this.callObjectBuiltin(recv, name, this.evalArgsLoose(n.args), line);
    }
    const args = this.evalMethodArgs(recv, name, n.args);
    return this.callMethod(recv, name, args, ref, n);
  };

  P.evalMethodArgs = function evalMethodArgs(recv, name, argNodes) {
    // brace-initialiser arguments take their type from the container's element type
    return argNodes.map((a) => {
      if (a.k === 'initlist') {
        const et = (recv && (recv.et || (recv instanceof MapObj && recv.vt))) || null;
        if (recv instanceof MapObj && (name === 'insert' || name === 'emplace')) return new Pair(recv.kt ? this.evalTyped(a.items[0], recv.kt) : this.evalAny(a.items[0]), recv.vt ? this.evalTyped(a.items[1], recv.vt) : this.evalAny(a.items[1]));
        if (et && et.k === 'type') return this.evalInitList(a, et);
        return this.evalAny(a);
      }
      return this.evalExpr(a);
    });
  };

  // ------------------------------------------------------------ invoke
  P.invoke = function invoke(fn, args, thisObj, line, isEntry = false, isCtor = false) {
    const savedFrame = this.frame, savedEnv = this.env;
    const v = this.invokeCore(fn, args, thisObj, line, isEntry, isCtor);
    this.frame = savedFrame; this.env = savedEnv;
    return v;
  };

  P.invokeCore = function invokeCore(fn, args, thisObj, line, isEntry, isCtor) {
    if (this.depth >= this.maxDepth) throw this.stackErr(line);
    const savedFrame = this.frame;
    const noTrace = !!fn.noTrace || this.quiet > 0;
    const fr = this.newFrame(fn, thisObj);
    if (!noTrace) { fr.fid = ++this.fidc; fr.pfid = savedFrame ? savedFrame.fid : -1; fr.depth = savedFrame ? savedFrame.depth + 1 : 0; } else if (savedFrame) { fr.fid = savedFrame.fid; fr.pfid = savedFrame.pfid; fr.depth = savedFrame.depth; }
    if (fn.noTrace) this.quiet++;
    fr.cls = (fn.cls && this.classes[fn.cls]) || (thisObj && thisObj.cls) || (savedFrame && savedFrame.cls) || null;
    if (thisObj && fn.cls && this.classes[fn.cls] && this.isSubclass(thisObj.cls, fn.cls)) fr.cls = this.classes[fn.cls];
    this.depth++;
    try {
      this.frame = fr; this.env = fr.env;
      const params = fn.params;
      for (let i = 0; i < params.length; i++) {
        const p = params[i];
        const ty = this.resolveType(p.type);
        if (p.type.varargs) { const rest = args.slice(i); const arr = rest.length === 1 && Array.isArray(rest[0]) ? rest[0] : rest; fr.env.vars.set(p.name, new Cell(arr, ty)); break; }
        let a;
        if (i < args.length) a = args[i];
        else if (p.def) a = this.evalTyped(p.def, ty);
        else throw new RuntimeError(`Missing argument ${i + 1} for "${fn.name}"`, line);
        if (this.lang === 'cpp' && ty.ref) fr.env.vars.set(p.name, isRef(a) ? a : new Cell(a, ty));
        else {
          if (isRef(a) && !ty.ptr && ty.name !== 'auto') a = a.get();
          fr.env.vars.set(p.name, new Cell(this.coerce(a, ty), ty));
        }
      }
      if (isCtor) this.runCtorPrologue(fn, thisObj, line);
      const r = this.execStmts(fn.body.stmts);
      let value;
      if (r instanceof Ret) value = r.v; else this.step(fn.body.endLine, 'return');
      if (value !== undefined && fn.ret && !isCtor) { const rt = this.resolveType(fn.ret); if (!(rt.ref && this.lang === 'cpp')) value = this.coerce(value, rt); }
      return value;
    } finally {
      if (fn.noTrace) this.quiet--;
      this.depth--;
    }
  };

  P.runCtorPrologue = function runCtorPrologue(fn, o, line) {
    const c = this.classes[fn.cls] || o.cls;
    const base = c.base ? this.classes[c.base.name] : null;
    const first = fn.body.stmts[0];
    const explicitSuper = first && first.k === 'expr' && first.expr.k === 'call' && ((first.expr.callee.k === 'id' && first.expr.callee.name === 'super') || first.expr.callee.k === 'this');
    const il = fn.initList || [];
    const baseInit = base ? il.find((x) => x.name === base.name) : null;
    if (base && !explicitSuper && !baseInit) this.construct(base, o, [], line);
    for (const it of il) {
      if (base && it.name === base.name) { this.construct(base, o, it.args.map((a) => this.evalExpr(a)), line); continue; }
      const fld = c.fields.find((f) => f.k === 'field' && f.name === it.name);
      if (!fld) { if (this.classes[it.name]) this.construct(this.classes[it.name], o, it.args.map((a) => this.evalExpr(a)), line); continue; }
      const ty = this.resolveType(fld.type);
      let v;
      if (it.args.length === 1) v = this.evalTyped(it.args[0], ty);
      else v = this.constructTyped(ty, it.args.map((a) => this.evalExpr(a)), false, line);
      o.f[it.name] = this.coerce(v, ty);
    }
  };

}
