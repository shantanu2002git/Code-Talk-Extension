// Tracing interpreter for the C++ / Java subset used by LeetCode and GeeksforGeeks solutions.
// It really executes the user's code (no scripted or invented states) and records a snapshot before every
// statement. Anything outside the supported subset raises a clear `Unsupported` error naming the line.
import { parse } from './parser.js';
import * as V from './values.js';
import { installLib } from './lib.js';

const {
  Dbl, Chr, Pair, Tup, Obj, UNINIT, Uninit, Cell, ElemRef, FieldRef, StrIdxRef, FnRef, MapObj, SetObj, Seq, Iter, Lambda,
  StrBuilder, RuntimeError, Unsupported, ThrowSignal, keyOf, equals, cloneVal, cloneObj, snap, toPlain, compare, hooks,
} = V;

export class BudgetError extends Error {
  constructor(message, kind) { super(message); this.kind = kind; this.type = 'Limit'; }
}

const BRK = { t: 'break' };
const CONT = { t: 'continue' };
class Ret { constructor(v) { this.t = 'ret'; this.v = v; } }

class Env {
  constructor(parent, flags = null) { this.parent = parent; this.vars = new Map(); if (flags) Object.assign(this, flags); }
  lookup(n) { for (let e = this; e; e = e.parent) { const r = e.vars.get(n); if (r !== undefined) return r; } return null; }
}

const PRELUDE = {
  cpp: `struct TreeNode { int val; TreeNode *left; TreeNode *right; TreeNode() : val(0), left(nullptr), right(nullptr) {} TreeNode(int x) : val(x), left(nullptr), right(nullptr) {} TreeNode(int x, TreeNode *l, TreeNode *r) : val(x), left(l), right(r) {} };
struct ListNode { int val; ListNode *next; ListNode() : val(0), next(nullptr) {} ListNode(int x) : val(x), next(nullptr) {} ListNode(int x, ListNode *n) : val(x), next(n) {} };`,
  java: `class TreeNode { int val; TreeNode left; TreeNode right; TreeNode() {} TreeNode(int val) { this.val = val; } TreeNode(int val, TreeNode left, TreeNode right) { this.val = val; this.left = left; this.right = right; } }
class ListNode { int val; ListNode next; ListNode() {} ListNode(int val) { this.val = val; } ListNode(int val, ListNode next) { this.val = val; this.next = next; } }`,
};

const NUMERIC = new Set(['int', 'long', 'double', 'char', 'bool', 'uint', 'ulong', 'uchar', 'short', 'Integer', 'Long', 'Double', 'Character', 'Boolean']);
const SEQ_NAMES = new Set(['vector', 'deque', 'list', 'array', 'forward_list', 'ArrayList', 'List', 'LinkedList', 'Vector', 'Collection', 'Iterable', 'ImmutableList']);

export class Interpreter {
  constructor(opts = {}) {
    this.lang = opts.lang || 'cpp';
    this.maxSteps = opts.maxSteps || 3000;
    this.maxOps = opts.maxOps || 6_000_000;
    this.maxDepth = opts.maxDepth || 220;
    this.deadline = opts.timeMs ? Date.now() + opts.timeMs : 0;
    this.steps = [];
    this.truncated = false;
    this.warnings = [];
    this.warned = new Set();
    this.classes = Object.create(null);
    this.funcs = Object.create(null);
    this.aliases = Object.create(null);
    this.genv = new Env(null, { fnRoot: true, isGlobal: true });
    this.globalDecls = [];
    this.frame = null;
    this.fidc = 0;
    this.depth = 0;
    this.quiet = 0;
    this.ops = 0;
    this.pendingOut = '';
    this.stdout = '';
    this.prec = 6;
    this.fixed = false;
    this.rngState = 123456789;
    this.maxCallsSeen = 0;
    hooks.coerce = (v, t) => this.coerce(v, t);
    installLib(this);
    this.env = this.genv;
    this.fidc = -1;
  }

  // ------------------------------------------------------------ loading
  load(src) {
    const prog = parse(src, this.lang);
    this.program = prog;
    const userNames = new Set();
    const collect = (items) => { for (const it of items) if (it.k === 'class') { userNames.add(it.name); collect(it.inner || []); } };
    collect(prog.items);
    this.registerItems(prog.items, false);
    const pre = PRELUDE[this.lang];
    if (pre && (!userNames.has('TreeNode') || !userNames.has('ListNode'))) {
      const items = parse(pre, this.lang).items.filter((c) => !userNames.has(c.name));
      for (const c of items) this.markPrelude(c);
      this.registerItems(items, true);
    }
    this.runGlobalInits();
  }

  markPrelude(c) {
    c.prelude = true;
    for (const m of [...c.methods, ...c.ctors]) m.noTrace = true;
  }

  registerItems(items, prelude) {
    for (const it of items) {
      if (it.k === 'class') this.registerClass(it, prelude);
      else if (it.k === 'func') { (this.funcs[it.name] ||= []).push(it); if (prelude) it.noTrace = true; } else if (it.k === 'typedef') this.aliases[it.name] = it.type;
      else if (it.k === 'field') this.globalDecls.push(it);
    }
  }

  registerClass(c, prelude) {
    this.classes[c.name] = c;
    c.statics = Object.create(null);
    c.staticTypes = Object.create(null);
    c.byName = Object.create(null);
    for (const m of c.methods) (c.byName[m.name] ||= []).push(m);
    for (const inn of c.inner || []) this.registerClass(inn, prelude);
    c.staticInitDone = false;
    this.pendingStatic = this.pendingStatic || [];
    this.pendingStatic.push(c);
    if (c.kind === 'enum') {
      c.enumConsts = Object.create(null);
    }
  }

  runGlobalInits() {
    const frame = this.newFrame({ name: '<global>', params: [] }, null);
    this.frame = frame;
    this.quiet++;
    try {
      for (const f of this.globalDecls) this.defineGlobal(f);
      for (const c of this.pendingStatic || []) this.initStatics(c);
      this.pendingStatic = [];
    } finally { this.quiet--; this.frame = null; }
  }

  defineGlobal(f) {
    const ty = this.resolveType(f.type);
    const v = this.initVar(ty, f.init, false, f.line);
    const cell = new Cell(v, this.refTy(ty));
    cell.global = true; cell.isConst = f.isConst; cell.name = f.name;
    this.genv.vars.set(f.name, cell);
    this.globalDecls2 = this.globalDecls2 || [];
    this.globalDecls2.push(f.name);
  }

  initStatics(c) {
    if (c.staticInitDone) return;
    c.staticInitDone = true;
    const prevFrame = this.frame;
    const fr = this.newFrame({ name: `${c.name}.<static>`, params: [] }, null);
    fr.cls = c;
    this.frame = fr;
    if (c.kind === 'enum') {
      c.enumConsts = c.enumConsts || Object.create(null);
      let next = 0;
      for (const ev of c.enumValues) {
        let v = ev.value ? this.toInt(this.evalExpr(ev.value)) : next;
        next = v + 1;
        if (this.lang === 'java') { const o = new Obj(c, { name: ev.name, ordinal: ev.ord }); o.enumName = ev.name; c.enumConsts[ev.name] = o; } else c.enumConsts[ev.name] = v;
      }
    }
    for (const f of c.fields) {
      if (f.k === 'init' && f.static) { this.quiet++; try { this.execBlockIn(f.body, new Env(fr.env)); } finally { this.quiet--; } continue; }
      if (f.k !== 'field' || !f.static) continue;
      const ty = this.resolveType(f.type);
      c.staticTypes[f.name] = this.refTy(ty);
      c.statics[f.name] = this.initVar(ty, f.init, false, f.line);
    }
    this.frame = prevFrame;
  }

  // ------------------------------------------------------------ types
  resolveType(ty) {
    if (!ty) return ty;
    const a = this.aliases[ty.name];
    if (a && ty.name !== a.name) {
      const base = this.resolveType(a);
      return { ...base, ptr: base.ptr + ty.ptr, ref: ty.ref || base.ref, dims: (base.dims || 0) + (ty.dims || 0), isConst: ty.isConst, arr: ty.arr || base.arr, args: ty.args && ty.args.length ? ty.args : base.args };
    }
    return ty;
  }

  /** type attached to a variable cell for implicit conversion on assignment */
  refTy(ty) {
    return ty || null;
  }

  isUserClass(name) { return name in this.classes; }

  toInt(v) {
    if (typeof v === 'number') return v;
    if (typeof v === 'bigint') return Number(v);
    if (v instanceof Chr) return v.c;
    if (v instanceof Dbl) return Math.trunc(v.v);
    if (typeof v === 'boolean') return v ? 1 : 0;
    if (v === UNINIT) return 0;
    if (v === null) throw new RuntimeError('NullPointerException: tried to use a null value as a number', this.line);
    throw new RuntimeError(`Expected a number but got ${this.describe(v)}`, this.line);
  }

  describe(v) {
    if (v === null) return 'null';
    if (typeof v === 'string') return 'a string';
    if (Array.isArray(v)) return 'an array';
    if (v instanceof Obj) return `an object of ${v.cls.name}`;
    return v && v.constructor ? v.constructor.name : typeof v;
  }

  num(v) { // numeric value as JS number (double math)
    if (typeof v === 'number') return v;
    if (v instanceof Dbl) return v.v;
    if (typeof v === 'bigint') return Number(v);
    if (v instanceof Chr) return v.c;
    if (typeof v === 'boolean') return v ? 1 : 0;
    if (v === UNINIT) return 0;
    throw new RuntimeError(`Expected a number but got ${this.describe(v)}`, this.line);
  }

  coerce(v, ty) {
    if (!ty || v === UNINIT) return v;
    if (ty.ptr || ty.dims || ty.arr) return v;
    switch (ty.name) {
      case 'int': case 'short': return this.wrap32(v);
      case 'long': return this.toLong(v);
      case 'double': return v instanceof Dbl ? v : new Dbl(this.num(v));
      case 'char': { if (v instanceof Chr) return v; const n = this.toInt(v); return Chr.of(this.lang === 'java' ? n & 0xFFFF : n & 0xFF); }
      case 'uchar': return Chr.of(this.toInt(v) & 0xFF);
      case 'bool': return typeof v === 'boolean' ? v : this.truthy(v);
      case 'uint': return this.toInt(v) >>> 0;
      case 'ulong': { if (typeof v === 'bigint') return v < 0n ? BigInt.asUintN(64, v) : v; const n = this.toInt(v); return n; }
      case 'Integer': return v === null ? null : this.wrap32(v);
      case 'Long': return v === null ? null : this.toLong(v);
      case 'Double': return v === null ? null : (v instanceof Dbl ? v : new Dbl(this.num(v)));
      case 'Character': return v === null ? null : (v instanceof Chr ? v : Chr.of(this.toInt(v)));
      case 'Boolean': return v;
      default: return v;
    }
  }

  wrap32(v) {
    if (typeof v === 'number') return v | 0;
    if (typeof v === 'bigint') return Number(BigInt.asIntN(32, v));
    if (v instanceof Chr) return v.c;
    if (v instanceof Dbl) { const x = v.v; if (Number.isNaN(x)) return 0; if (this.lang === 'java') return x >= 2147483647 ? 2147483647 : x <= -2147483648 ? -2147483648 : Math.trunc(x); return Math.trunc(x) | 0; }
    if (typeof v === 'boolean') return v ? 1 : 0;
    if (v === null) throw new RuntimeError('NullPointerException: a null value was used as an int', this.line);
    return this.toInt(v);
  }

  toLong(v) {
    if (typeof v === 'bigint') return BigInt.asIntN(64, v);
    if (typeof v === 'number') return BigInt(v);
    if (v instanceof Chr) return BigInt(v.c);
    if (v instanceof Dbl) { const x = v.v; if (!Number.isFinite(x)) return 0n; return BigInt.asIntN(64, BigInt(Math.trunc(x))); }
    if (typeof v === 'boolean') return v ? 1n : 0n;
    if (v === null) throw new RuntimeError('NullPointerException: a null value was used as a long', this.line);
    return BigInt(this.toInt(v));
  }

  truthy(v) {
    if (typeof v === 'boolean') return v;
    if (typeof v === 'number') return v !== 0;
    if (v === null || v === undefined) return false;
    if (typeof v === 'bigint') return v !== 0n;
    if (v instanceof Dbl) return v.v !== 0;
    if (v instanceof Chr) return v.c !== 0;
    if (v === UNINIT) return false;
    return true;
  }

  defaultValue(ty, uninit = false) {
    ty = this.resolveType(ty);
    if (ty.arr && ty.arr.length) return this.makeCArray(ty, ty.arr.map((e) => (e ? this.toInt(this.evalExpr(e)) : 0)), uninit);
    if (ty.ptr) return null;
    if (ty.dims) { const a = []; a.et = { ...ty, dims: ty.dims - 1 }; return null; }
    const n = ty.name;
    switch (n) {
      case 'int': case 'short': return uninit ? UNINIT : 0;
      case 'uint': case 'ulong': return uninit ? UNINIT : 0;
      case 'long': return uninit ? UNINIT : 0n;
      case 'double': return uninit ? UNINIT : new Dbl(0);
      case 'char': case 'uchar': return uninit ? UNINIT : Chr.of(0);
      case 'bool': return uninit ? UNINIT : false;
      case 'string': return this.lang === 'java' ? null : '';
      case 'Integer': case 'Long': case 'Double': case 'Character': case 'Boolean': case 'Object': return null;
      case 'auto': case 'var': return null;
      default: break;
    }
    if (this.lang === 'java') {
      if (n === 'StringBuilder' || n === 'StringBuffer') return new StrBuilder('');
      return null;
    }
    return this.constructType(ty, []);
  }

  makeCArray(ty, dims, uninit) {
    const base = { ...ty, arr: null, ptr: ty.ptr };
    const build = (k) => {
      const a = [];
      if (k === dims.length - 1) { a.et = base; for (let i = 0; i < dims[k]; i++) a.push(this.defaultValue(base, uninit)); } else { a.et = { ...base, arr: new Array(dims.length - k - 1).fill(null) }; for (let i = 0; i < dims[k]; i++) a.push(build(k + 1)); }
      return a;
    };
    return build(0);
  }

  // build a container / object of a (C++ or Java) type from constructor args
  constructType(ty, args, line) {
    ty = this.resolveType(ty);
    const n = ty.name;
    const a0 = ty.args && ty.args[0];
    const withEt = (arr) => { if (a0 && a0.k === 'type') arr.et = this.resolveType(a0); return arr; };
    const L = this.lang;
    if (this.isUserClass(n)) return this.instantiate(this.classes[n], args, line);
    if (SEQ_NAMES.has(n)) {
      const arr = withEt([]);
      if (n === 'array') { const sz = ty.args[1] && ty.args[1].k === 'num' ? Number(ty.args[1].value) : 0; for (let i = 0; i < sz; i++) arr.push(this.defaultValue(a0)); return arr; }
      if (args.length === 0) return arr;
      const x = args[0];
      if (typeof x === 'number' || typeof x === 'bigint') { // vector<T>(n [, v])
        const cnt = Number(x);
        if (cnt < 0) throw new RuntimeError('length_error: negative vector size', line);
        if (cnt > 5_000_000) throw new RuntimeError('Vector too large for the visualizer', line);
        for (let i = 0; i < cnt; i++) arr.push(args.length > 1 ? cloneVal(this.coerce(args[1], arr.et)) : this.defaultValue(a0));
        return arr;
      }
      if (Array.isArray(x)) { const c = x.map((e) => cloneVal(this.coerce(e, arr.et))); c.et = arr.et || x.et; return args.length > 1 && args[1] instanceof Iter ? this.sliceIter(x, args) : c; }
      if (x instanceof Iter) return withEt(this.sliceIter(null, args));
      if (x instanceof Seq) return withEt(x.a.map(cloneVal));
      if (x instanceof SetObj) return withEt(x.keys().map(cloneVal));
      if (x instanceof MapObj) return withEt(x.entries().map(cloneVal));
      return arr;
    }
    switch (n) {
      case 'pair': case 'Pair': case 'Entry': { const p = new Pair(args.length ? this.coerce(args[0], this.resolveType(ty.args[0])) : this.defaultValue(ty.args[0]), args.length > 1 ? this.coerce(args[1], this.resolveType(ty.args[1])) : this.defaultValue(ty.args[1])); return p; }
      case 'tuple': return new Tup(ty.args.map((t, i) => (i < args.length ? this.coerce(args[i], this.resolveType(t)) : this.defaultValue(t))));
      case 'string': {
        if (L === 'java') { if (args.length === 0) return ''; const x = args[0]; if (Array.isArray(x)) return x.map((c) => (c instanceof Chr ? c.s : String.fromCharCode(c))).join(''); return String(this.str(x)); }
        if (args.length === 0) return '';
        if (typeof args[0] === 'string') return args.length > 1 ? args[0].substr(this.toInt(args[1]), args.length > 2 ? this.toInt(args[2]) : undefined) : args[0];
        if (typeof args[0] === 'number') return (args[1] instanceof Chr ? args[1].s : String.fromCharCode(this.toInt(args[1]))).repeat(args[0]);
        if (args[0] instanceof Iter) return this.rangeStr(args[0], args[1]);
        return '';
      }
      case 'StringBuilder': case 'StringBuffer': return new StrBuilder(args.length && typeof args[0] === 'string' ? args[0] : '');
      case 'map': case 'multimap': case 'TreeMap': case 'unordered_map': case 'HashMap': case 'LinkedHashMap': case 'Hashtable': case 'ConcurrentHashMap': case 'unordered_multimap': case 'SortedMap': case 'NavigableMap': case 'Map': {
        const ordered = n === 'map' || n === 'multimap' || n === 'TreeMap' || n === 'SortedMap' || n === 'NavigableMap';
        const m = new MapObj(ordered ? 'map' : 'umap', ordered, null);
        m.kt = ty.args[0] ? this.resolveType(ty.args[0]) : null; m.vt = ty.args[1] ? this.resolveType(ty.args[1]) : null;
        if (L === 'java' && (n === 'HashMap' || n === 'Hashtable' || n === 'ConcurrentHashMap' || n === 'Map')) m.jhash = true;
        if (n === 'multimap' || n === 'unordered_multimap') m.multi = true;
        const cmpArg = args.find((x) => x instanceof Lambda || x instanceof FnRef || x instanceof Obj);
        const cmpT = this.cmpFromTypeArg(ty.args[2]);
        if (cmpArg) m.cmp = this.makeCmp(cmpArg); else if (cmpT) m.cmp = cmpT; else if (ordered) m.cmp = (a, b) => this.cmpVals(a, b);
        const src = args.find((x) => x instanceof MapObj);
        if (src) for (const e of src.entries()) this.mapPut(m, cloneVal(e.first), cloneVal(e.second));
        return m;
      }
      case 'set': case 'multiset': case 'TreeSet': case 'unordered_set': case 'HashSet': case 'LinkedHashSet': case 'unordered_multiset': case 'SortedSet': case 'NavigableSet': case 'Set': {
        const ordered = n === 'set' || n === 'multiset' || n === 'TreeSet' || n === 'SortedSet' || n === 'NavigableSet';
        const s = new SetObj('set', ordered, null);
        s.kt = a0 ? this.resolveType(a0) : null;
        if (L === 'java' && (n === 'HashSet' || n === 'Set')) s.jhash = true;
        if (n === 'multiset' || n === 'unordered_multiset') s.multi = true;
        const cmpArg = args.find((x) => x instanceof Lambda || x instanceof FnRef || (x instanceof Obj && !(x.cls.prelude)));
        const cmpT = this.cmpFromTypeArg(ty.args[1]);
        if (cmpArg) s.cmp = this.makeCmp(cmpArg); else if (cmpT) s.cmp = cmpT; else if (ordered) s.cmp = (a, b) => this.cmpVals(a, b);
        for (let ai = 0; ai < args.length; ai++) {
          const x = args[ai];
          if (Array.isArray(x)) for (const e of x) this.setAdd(s, e);
          else if (x instanceof SetObj) for (const e of x.keys()) this.setAdd(s, e);
          else if (x instanceof Seq) for (const e of x.a) this.setAdd(s, e);
          else if (x instanceof Iter && args[ai + 1] instanceof Iter) { for (const e of this.iterToArray(x, args[ai + 1])) this.setAdd(s, e); ai++; }
        }
        return s;
      }
      case 'stack': case 'Stack': { const q = new Seq('stack'); q.et = a0 ? this.resolveType(a0) : null; return q; }
      case 'queue': case 'Queue': { const q = new Seq('queue'); q.et = a0 ? this.resolveType(a0) : null; const src = args[0]; if (src instanceof Seq) q.a = src.a.map(cloneVal); return q; }
      case 'ArrayDeque': case 'Deque': { const q = new Seq('deque'); q.et = a0 ? this.resolveType(a0) : null; if (Array.isArray(args[0])) q.a = args[0].slice(); else if (args[0] instanceof Seq) q.a = args[0].a.slice(); return q; }
      case 'LinkedList': { const q = new Seq('deque'); q.et = a0 ? this.resolveType(a0) : null; if (Array.isArray(args[0])) q.a = args[0].slice(); else if (args[0] instanceof Seq) q.a = args[0].a.slice(); return q; }
      case 'priority_queue': case 'PriorityQueue': { return this.makePQ(ty, args); }
      case 'function': case 'Function': case 'BiFunction': case 'Supplier': case 'Consumer': case 'Predicate': case 'Comparator': case 'Runnable': return null;
      case 'Random': { const r = new V.Rng(); if (args.length) r.s = this.toInt(args[0]) || 1; return r; }
      case 'Scanner': case 'BufferedReader': throw new Unsupported('Reading input (Scanner / BufferedReader / cin) is not supported — LeetCode and GFG solutions are called with arguments', line);
      case 'int': case 'long': case 'double': case 'char': case 'bool': case 'short': case 'uint': case 'ulong': case 'uchar': return this.coerce(args.length ? args[0] : this.defaultValue(ty), ty);
      case 'Integer': case 'Long': case 'Double': case 'Character': case 'Boolean': return this.coerce(args[0], ty);
      case 'Object': return new Obj({ name: 'Object', fields: [], methods: [], ctors: [], byName: {}, statics: {} }, {});
      case 'bitset': throw new Unsupported('bitset is not supported by the visualizer yet', line);
      case 'optional': return null;
      default: {
        const fo = this.stdFunctor(n); if (fo) return fo;
        if (this.builtinFreeExists(n)) return this.callBuiltinValues(n, args, line);
      }
        if (/Exception$|Error$|^runtime_error$|^exception$|^logic_error$|^invalid_argument$|^out_of_range$/.test(n)) return this.makeException(n, args.length ? this.str(args[0]) : '');
        throw new Unsupported(`The type "${n}" is not supported by the visualizer`, line);
    }
  }

  makeException(name, msg) {
    const cls = { name, fields: [], methods: [], ctors: [], byName: {}, statics: {}, builtinException: true, base: null, kind: 'class' };
    return new Obj(cls, { message: msg });
  }

  cmpFromTypeArg(t) {
    if (!t || t.k !== 'type') return null;
    const n = t.name;
    if (n === 'greater') return (a, b) => this.cmpVals(b, a);
    if (n === 'less') return (a, b) => this.cmpVals(a, b);
    if (this.isUserClass(n)) { const o = this.instantiate(this.classes[n], []); return this.makeCmp(o); }
    return null;
  }

  makePQ(ty, args) {
    const q = new Seq('pq');
    const a0 = ty.args && ty.args[0];
    q.et = a0 && a0.k === 'type' ? this.resolveType(a0) : null;
    let cmpFn = null; // returns <0 when `a` leaves the queue before `b`
    const cArg = args.find((x) => x instanceof Lambda || x instanceof FnRef || (x instanceof Obj));
    if (this.lang === 'java') {
      cmpFn = cArg ? this.makeCmp(cArg) : (a, b) => this.cmpVals(a, b);
    } else {
      let less;
      if (cArg) less = this.makeCmp(cArg); else if (ty.args[2]) { less = this.cmpFromTypeArg(ty.args[2]); }
      if (!less) less = (a, b) => this.cmpVals(a, b);
      // comp(a,b) true => a has lower priority than b
      cmpFn = (a, b) => { const x = less(b, a); if (x < 0 || x === true) return 1; const y = less(a, b); return (y < 0 || y === true) ? -1 : 0; };
      // `less` returns int (<0 / 0 / >0) for builtin comparators or boolean-as-int for user comparators; normalise below
      const raw = less;
      cmpFn = (a, b) => { const ab = this.lessBool(raw, a, b); if (ab) return 1; const ba = this.lessBool(raw, b, a); return ba ? -1 : 0; };
    }
    q.cmp = cmpFn;
    for (let ai = 0; ai < args.length; ai++) {
      const x = args[ai];
      if (Array.isArray(x)) for (const e of x) this.pqPush(q, e);
      else if (x instanceof Seq) for (const e of x.a) this.pqPush(q, e);
      else if (x instanceof Iter && args[ai + 1] instanceof Iter) { for (const e of this.iterToArray(x, args[ai + 1])) this.pqPush(q, e); ai++; }
    }
    return q;
  }

  lessBool(fn, a, b) { const r = fn(a, b); return typeof r === 'boolean' ? r : r < 0; }

  pqPush(q, v) {
    const a = q.a;
    let lo = 0, hi = a.length;
    while (lo < hi) { const mid = (lo + hi) >> 1; if (q.cmp(a[mid], v) <= 0) lo = mid + 1; else hi = mid; }
    a.splice(lo, 0, v);
  }

  /** wrap a callable (lambda, function object, function pointer) into a JS comparator returning a number or boolean */
  makeCmp(f) {
    let call;
    if (f instanceof Obj) {
      const m = this.findMethod(f.cls, 'operator()', 2) || this.findMethod(f.cls, 'compare', 2);
      if (!m) throw new Unsupported('Comparator object has no operator() / compare', this.line);
      call = (a, b) => this.invoke(m, [a, b], f, this.line);
    } else call = (a, b) => this.callValue(f, [a, b]);
    return (a, b) => { const r = call(a, b); if (typeof r === 'boolean') return r ? -1 : (call(b, a) === true ? 1 : 0); return this.toInt(r); };
  }

  // ------------------------------------------------------------ frames, steps
  newFrame(fn, thisObj, parent = null) {
    return { fn, name: fn.name || 'lambda', fid: 0, pfid: -1, depth: 0, thisObj, env: new Env(this.genv, { fnRoot: true }), cls: thisObj ? thisObj.cls : null, retType: fn.ret || null };
  }

  step(line, ev = 'line', ret, hasRet = false) {
    if (this.quiet) return null;
    if (this.steps.length >= this.maxSteps) { this.truncated = true; return null; }
    const fr = this.frame;
    const heap = {};
    const vars = {};
    this.collectVars(fr.env, vars, heap);
    const st = { i: this.steps.length, line, fn: fr.name, depth: fr.depth, fid: fr.fid, pfid: fr.pfid, ev, vars };
    const members = this.collectMembers(fr, heap);
    if (members) st.members = members;
    if (Object.keys(heap).length) st.heap = heap;
    if (hasRet) st.ret = snap(ret, heap);
    if (this.pendingOut) { st.out = this.pendingOut; this.pendingOut = ''; }
    this.steps.push(st);
    return st;
  }

  collectVars(env, out, heap) {
    const chain = [];
    for (let e = env; e && !e.isGlobal; e = e.parent) {
      chain.push(e);
      if (e.fnRoot && !e.isLambda) break;
    }
    for (let i = chain.length - 1; i >= 0; i--) {
      for (const [k, ref] of chain[i].vars) {
        if (k === '__this') continue;
        out[k] = snap(ref.get(), heap);
      }
    }
  }

  collectMembers(fr, heap) {
    let out = null;
    const t = fr.thisObj;
    if (t && t.f && !t.cls.prelude) {
      const keys = Object.keys(t.f);
      if (keys.length && !(this.isNodeLike(t))) { out = {}; for (const k of keys) out[k] = snap(t.f[k], heap); }
    }
    const c = fr.cls;
    if (c && c.statics) for (const [k, v] of Object.entries(c.statics)) { out = out || {}; out[k] = snap(v, heap); }
    if (this.globalDecls2) for (const k of this.globalDecls2) { const cell = this.genv.vars.get(k); if (cell && !cell.isConst) { out = out || {}; out[k] = snap(cell.get(), heap); } }
    return out;
  }

  isNodeLike(o) { const f = o.f; return ('val' in f || 'data' in f || 'key' in f) && ('next' in f || 'left' in f || 'right' in f) && Object.keys(f).length <= 4; }

  // ------------------------------------------------------------ entry
  /** Run `entry` with already converted runtime arguments. Returns the raw result. */
  runEntry(fnName, args, opts = {}) {
    const cands = this.entryCandidates(fnName);
    if (!cands.length) throw new RuntimeError(`Function "${fnName}" was not found in the code`, 1);
    const fn = cands.find((c) => c.params.length === args.length) || cands[0];
    let thisObj = null;
    if (fn.cls && this.classes[fn.cls] && !fn.isStatic) thisObj = this.instantiate(this.classes[fn.cls], [], fn.line);
    const top = this.newFrame({ name: '<root>', params: [] }, null);
    top.fid = -1; top.pfid = -2;
    this.frame = top;
    const ref = args.map((a, i) => (fn.params[i] && fn.params[i].type.ref ? new Cell(a, null) : a));
    const r = this.invoke(fn, ref, thisObj, fn.line, true);
    this.frame = null;
    return { value: r, fn };
  }

  entryCandidates(name) {
    const out = [];
    if (this.funcs[name]) out.push(...this.funcs[name]);
    for (const c of Object.values(this.classes)) if (!c.prelude && c.byName[name]) out.push(...c.byName[name]);
    return out;
  }

  // ------------------------------------------------------------ objects & classes
  allFields(c) {
    const chain = [];
    for (let k = c; k; k = k.base ? this.classes[k.base.name] : null) { chain.unshift(k); if (chain.length > 20) break; }
    return chain;
  }

  instantiate(c, args, line) {
    if (c.kind === 'interface') throw new RuntimeError(`Cannot create an instance of interface ${c.name}`, line);
    const o = new Obj(c, {});
    const chain = this.allFields(c);
    const prevFrame = this.frame;
    const fr = this.newFrame({ name: `${c.name}.<init>`, params: [] }, o);
    fr.fid = prevFrame ? prevFrame.fid : 0; fr.pfid = prevFrame ? prevFrame.pfid : -1; fr.depth = prevFrame ? prevFrame.depth : 0;
    this.frame = fr;
    this.quiet++;
    try {
      for (const k of chain) {
        for (const f of k.fields) {
          if (f.k === 'init' && !f.static) { this.execBlockIn(f.body, new Env(fr.env)); continue; }
          if (f.k !== 'field' || f.static) continue;
          const ty = this.resolveType(f.type);
          o.f[f.name] = this.initVar(ty, f.init, false, f.line);
          (o.types ||= {})[f.name] = this.refTy(ty);
        }
      }
    } finally { this.quiet--; this.frame = prevFrame; }
    this.construct(c, o, args, line);
    return o;
  }

  construct(c, o, args, line) {
    const ctors = c.ctors;
    if (!ctors.length) {
      if (c.base) { const b = this.classes[c.base.name]; if (b) this.construct(b, o, [], line); }
      if (args.length && c.kind !== 'enum') { // aggregate initialisation: Node{1, nullptr}
        const names = c.fields.filter((f) => f.k === 'field' && !f.static).map((f) => f);
        args.forEach((a, i) => { if (names[i]) o.f[names[i].name] = this.coerce(a, this.resolveType(names[i].type)); });
      }
      return;
    }
    const ct = this.pickOverload(ctors, args, line, c.name);
    this.invoke(ct, args, o, line, false, true);
  }

  findMethod(cls, name, argc, args) {
    for (let k = cls; k; k = k.base ? this.classes[k.base.name] : null) {
      const list = k.byName && k.byName[name];
      if (list) { const m = this.pickOverload(list, args || new Array(argc).fill(null), this.line, name, true); if (m) return m; }
    }
    // interface default methods
    for (let k = cls; k; k = k.base ? this.classes[k.base.name] : null) { void k; break; }
    return null;
  }

  pickOverload(list, args, line, name, soft = false) {
    const n = args.length;
    let cands = list.filter((f) => f.params.length === n || (f.params.length > n && f.params.slice(n).every((p) => p.def)) || (f.params.length && f.params[f.params.length - 1].type.varargs && n >= f.params.length - 1));
    if (!cands.length) { if (soft) return null; throw new RuntimeError(`No matching overload of "${name}" for ${n} argument(s)`, line); }
    if (cands.length === 1) return cands[0];
    let best = cands[0], bs = -1;
    for (const f of cands) {
      let s = f.params.length === n ? 5 : 0;
      for (let i = 0; i < n && i < f.params.length; i++) s += this.typeScore(f.params[i].type, args[i]);
      if (s > bs) { bs = s; best = f; }
    }
    return best;
  }

  typeScore(ty, v) {
    ty = this.resolveType(ty);
    if (v === null) return ty.ptr || !NUMERIC.has(ty.name) ? 2 : 0;
    if (ty.dims || ty.ptr || ty.arr) return Array.isArray(v) || v === null ? 3 : (v instanceof Obj && ty.ptr ? 3 : 0);
    switch (ty.name) {
      case 'int': case 'short': case 'Integer': return typeof v === 'number' ? 4 : v instanceof Chr ? 2 : typeof v === 'boolean' ? 1 : 0;
      case 'long': case 'Long': case 'ulong': return typeof v === 'bigint' ? 4 : typeof v === 'number' ? 3 : 0;
      case 'double': case 'Double': return v instanceof Dbl ? 4 : typeof v === 'number' || typeof v === 'bigint' ? 2 : 0;
      case 'char': case 'Character': return v instanceof Chr ? 4 : 0;
      case 'bool': case 'Boolean': return typeof v === 'boolean' ? 4 : 0;
      case 'string': return typeof v === 'string' ? 4 : 0;
      default:
        if (this.isUserClass(ty.name)) return v instanceof Obj ? (this.isSubclass(v.cls, ty.name) ? 4 : 0) : 0;
        if (SEQ_NAMES.has(ty.name)) return Array.isArray(v) ? 4 : 0;
        if (/map|Map/.test(ty.name)) return v instanceof MapObj ? 4 : 0;
        if (/set|Set/.test(ty.name)) return v instanceof SetObj ? 4 : 0;
        return 1;
    }
  }

  isSubclass(c, name) {
    for (let k = c; k; k = k.base ? this.classes[k.base.name] : null) { if (k.name === name) return true; }
    return false;
  }

  /** value for a declaration `T x = init` / field / return */
  initVar(ty, init, isLocal, line) {
    if (!init) return this.defaultValue(ty, isLocal && this.lang === 'cpp');
    if (init.k === 'ctorcall') {
      if (init.brace) return this.coerce(this.evalInitList({ k: 'initlist', items: init.args, line: init.line }, ty), ty);
      const args = init.args.map((a) => this.evalExpr(a));
      return this.valueForType(this.constructTyped(ty, args, init.brace, line), ty);
    }
    return this.evalTyped(init, ty);
  }

  constructTyped(ty, args, brace, line) {
    ty = this.resolveType(ty);
    if (brace && SEQ_NAMES.has(ty.name) && ty.name !== 'array') { const a = args.map((e) => cloneVal(this.coerce(e, this.resolveType(ty.args[0])))); if (ty.args[0]) a.et = this.resolveType(ty.args[0]); return a; }
    return this.constructType(ty, args, line);
  }

  valueForType(v, ty) {
    return this.coerce(v, ty);
  }

  /** evaluate `node` where a value of type `ty` is expected (handles brace initialisers and C++ copy semantics) */
  evalTyped(node, ty) {
    ty = this.resolveType(ty);
    if (node.k === 'initlist') return this.evalInitList(node, ty);
    if (ty.name === 'auto' || ty.name === 'var') { const v = this.evalExpr(node); return this.copyIfValue(v, ty); }
    const v = this.evalExpr(node);
    if (node.k === 'null' && ty.ptr === 0 && ty.name !== 'string' && this.lang === 'cpp' && NUMERIC.has(ty.name)) return this.coerce(0, ty);
    return this.copyIfValue(this.coerce(v, ty), ty);
  }

  copyIfValue(v, ty) {
    if (this.lang !== 'cpp' || ty.ref || ty.ptr) return v;
    if (v !== null && typeof v === 'object') { if (v instanceof Obj) return v.heap || v.addrTaken ? v : cloneObj(v); return cloneVal(v); }
    return v;
  }

  evalInitList(node, ty) {
    ty = this.resolveType(ty);
    const items = node.items;
    if (ty.arr && ty.arr.length) { // int a[3] = {1,2,3} / int dp[2][2] = {{1,2},{3,4}}
      const dims = ty.arr.map((e, i) => (e ? this.toInt(this.evalExpr(e)) : (i === 0 ? items.length : 0)));
      const arr = this.makeCArray(ty, dims, false);
      const fill = (a, its, k) => {
        its.forEach((it, i) => {
          if (it.k === 'initlist' && Array.isArray(a[i])) fill(a[i], it.items, k + 1);
          else if (i < a.length) a[i] = this.coerce(this.evalExpr(it), a.et);
        });
      };
      fill(arr, items, 0);
      return arr;
    }
    if (ty.dims) { // Java: int[] a = {1,2,3}
      const et = { ...ty, dims: ty.dims - 1 };
      const a = items.map((it) => (it.k === 'initlist' ? this.evalInitList(it, et) : this.coerce(this.evalExpr(it), et)));
      a.et = et;
      return a;
    }
    const n = ty.name;
    if (SEQ_NAMES.has(n) && n !== 'array') {
      const et = ty.args[0] ? this.resolveType(ty.args[0]) : null;
      const a = items.map((it) => cloneVal(et ? this.evalTyped(it, et) : this.evalExpr(it)));
      if (et) a.et = et;
      return a;
    }
    if (n === 'array') { const et = this.resolveType(ty.args[0]); const sz = ty.args[1] && ty.args[1].k === 'num' ? Number(ty.args[1].value) : items.length; const a = []; a.et = et; for (let i = 0; i < sz; i++) a.push(i < items.length ? this.evalTyped(items[i], et) : this.defaultValue(et)); return a; }
    if (n === 'pair') return new Pair(this.evalTyped(items[0], ty.args[0]), this.evalTyped(items[1], ty.args[1]));
    if (n === 'tuple') return new Tup(items.map((it, i) => this.evalTyped(it, ty.args[i] || { k: 'type', name: 'auto', args: [], ptr: 0, ref: false, dims: 0 })));
    if (/^(map|unordered_map|multimap|TreeMap|HashMap)$/.test(n)) {
      const m = this.constructType(ty, [], node.line);
      for (const it of items) { const k = this.evalTyped(it.items[0], ty.args[0]); const v = this.evalTyped(it.items[1], ty.args[1]); this.mapPut(m, k, v); }
      return m;
    }
    if (/^(set|unordered_set|multiset|TreeSet|HashSet)$/.test(n)) {
      const s = this.constructType(ty, [], node.line);
      for (const it of items) this.setAdd(s, this.evalTyped(it, ty.args[0]));
      return s;
    }
    if (this.isUserClass(n)) { const c = this.classes[n]; return this.instantiate(c, items.map((it, i) => this.evalAny(it)), node.line); }
    if (NUMERIC.has(n) && items.length === 1) return this.coerce(this.evalExpr(items[0]), ty);
    if (n === 'auto' || n === 'var') return items.map((it) => this.evalExpr(it));
    if (n === 'string') return items.map((it) => { const v = this.evalExpr(it); return v instanceof Chr ? v.s : String(v); }).join('');
    if (items.length === 0) return this.defaultValue(ty);
    return items.map((it) => this.evalExpr(it));
  }

  evalAny(node) { return node.k === 'initlist' ? node.items.map((it) => this.evalAny(it)) : this.evalExpr(node); }
}

export { Env, BRK, CONT, Ret, NUMERIC, SEQ_NAMES };
import { installExec } from './exec.js';
installExec(Interpreter);
