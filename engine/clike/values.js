// Runtime values of the C++/Java interpreter and helpers (copying, equality, ordering, JSON snapshots).
//
// Representation:
//   int / short / byte / Integer .... JS number (integral)       long / long long ..... BigInt
//   double / float .................. Dbl                         char ................. Chr (cached per code)
//   bool ............................ JS boolean                  string / String ...... JS string
//   vector / array / list ........... JS Array                    pair / Map.Entry ..... Pair
//   map / set ....................... MapObj / SetObj             stack / queue / pq ... Seq
//   user class / struct instance .... Obj                         nullptr / null ....... null

export class Dbl { constructor(v) { this.v = v; } }
const chrCache = [];
export class Chr {
  constructor(c) { this.c = c; }
  static of(c) { return chrCache[c] || (chrCache[c] = new Chr(c)); }
  static from(s) { return Chr.of(s.charCodeAt(0)); }
  get s() { return String.fromCharCode(this.c); }
}
export class Pair {
  constructor(first, second) { this.first = first; this.second = second; }
}
export class Tup { constructor(items) { this.items = items; } }
export class Obj {
  constructor(cls, fields = {}) { this.cls = cls; this.f = fields; this.id = ++Obj.counter; }
}
Obj.counter = 0;
export class Uninit { constructor(type) { this.type = type; } }
export const UNINIT = new Uninit();

export const hooks = { coerce: null };
export class Cell {
  constructor(v, ty = null) { this.v = v; this.ty = ty; }
  get() { return this.v; }
  set(x) { this.v = this.ty && hooks.coerce ? hooks.coerce(x, this.ty) : x; }
}
export class ElemRef {
  constructor(arr, i) { this.arr = arr; this.i = i; }
  get() { return this.arr[this.i]; }
  set(x) { this.arr[this.i] = this.arr.et && hooks.coerce ? hooks.coerce(x, this.arr.et) : x; }
}
export class FieldRef {
  constructor(o, name, ty = null) { this.o = o; this.name = name; this.ty = ty; }
  get() { return this.o[this.name]; }
  set(x) { this.o[this.name] = this.ty && hooks.coerce ? hooks.coerce(x, this.ty) : x; }
}
/** s[i] where s lives in a variable: strings are immutable JS primitives, so writes rebuild the string */
export class StrIdxRef {
  constructor(ref, i) { this.ref = ref; this.i = i; }
  get() { return Chr.of(this.ref.get().charCodeAt(this.i)); }
  set(x) { const s = this.ref.get(); const c = x instanceof Chr ? x.s : String.fromCharCode(typeof x === 'number' ? x : Number(x)); this.ref.set(s.slice(0, this.i) + c + s.slice(this.i + 1)); }
}
export class FnRef { // plain function value (lambda / function pointer / method reference)
  constructor(call, name) { this.call = call; this.name = name; }
}

/** Ordered hash map / set. Keys are compared by value. */
export function javaHash(v) {
  if (v === null || v === undefined) return 0;
  if (typeof v === 'number') return v | 0;
  if (typeof v === 'bigint') { const x = BigInt.asUintN(64, v); return Number(BigInt.asIntN(32, x ^ (x >> 32n))); }
  if (typeof v === 'boolean') return v ? 1231 : 1237;
  if (typeof v === 'string') { let h = 0; for (let i = 0; i < v.length; i++) h = (Math.imul(31, h) + v.charCodeAt(i)) | 0; return h; }
  if (v instanceof Chr) return v.c;
  if (v instanceof Dbl) { const b = new DataView(new ArrayBuffer(8)); b.setFloat64(0, v.v); const x = b.getInt32(0) ^ b.getInt32(4); return x | 0; }
  if (Array.isArray(v)) { let h = 1; for (const x of v) h = (Math.imul(31, h) + javaHash(x)) | 0; return h; }
  if (v instanceof Pair) return (javaHash(v.first) ^ javaHash(v.second)) | 0;
  if (v instanceof Obj) return (v.id * 2654435761) | 0;
  return 0;
}
/** Java HashMap / HashSet iteration order: bucket index (spread hash & (capacity-1)), insertion order inside a bucket. */
function jorder(items, keyFn, cap) {
  const idx = (x) => { const h = javaHash(keyFn(x)); return ((h ^ (h >>> 16)) & (cap - 1)) >>> 0; };
  return items.map((x, i) => [idx(x), i, x]).sort((a, b) => a[0] - b[0] || a[1] - b[1]).map((t) => t[2]);
}
export class MapObj {
  constructor(kind = 'map', ordered = false, cmp = null) { this.kind = kind; this.ordered = ordered; this.m = new Map(); this.cmp = cmp; this.kt = null; this.vt = null; this.jhash = false; this.cap = 16; }
  dirty() { this._c = null; }
  entries() {
    if (this._c) return this._c;
    let es = [...this.m.values()];
    if (this.ordered) es.sort((a, b) => (this.cmp ? this.cmp(a.first, b.first) : compare(a.first, b.first)));
    else if (this.jhash) es = jorder(es, (e) => e.first, this.cap);
    this._c = es;
    return es;
  }
  grow() { while (this.m.size > this.cap * 0.75) this.cap *= 2; }
  get size() { return this.m.size; }
}
export class SetObj {
  constructor(kind = 'set', ordered = false, cmp = null) { this.kind = kind; this.ordered = ordered; this.m = new Map(); this.cmp = cmp; this.kt = null; this.jhash = false; this.cap = 16; }
  dirty() { this._c = null; }
  keys() {
    if (this._c) return this._c;
    let ks = [...this.m.values()];
    if (this.ordered) ks.sort(this.cmp || compare);
    else if (this.jhash) ks = jorder(ks, (k) => k, this.cap);
    this._c = ks;
    return ks;
  }
  grow() { while (this.m.size > this.cap * 0.75) this.cap *= 2; }
  get size() { return this.m.size; }
}
/** stack / queue / deque / priority_queue / Stack / ArrayDeque / PriorityQueue / LinkedList-as-queue */
export class Seq {
  constructor(kind, cmp = null) { this.kind = kind; this.a = []; this.cmp = cmp; this.et = null; }
}
export class Iter {
  constructor(coll, pos, keys = null, rev = false) { this.coll = coll; this.pos = pos; this.keys = keys; this.rev = rev; }
}
export class Lambda { constructor(node, env, thisObj, frameInfo) { this.node = node; this.env = env; this.thisObj = thisObj; this.frameInfo = frameInfo; } }
export class StrBuilder { constructor(s = '') { this.s = s; } }
export class Rng { constructor() { this.s = 12345; } }

export class RuntimeError extends Error {
  constructor(message, line, type = 'RuntimeError') { super(message); this.line = line; this.type = type; this.kind = 'runtime'; }
}
export class Unsupported extends Error {
  constructor(message, line) { super(message); this.line = line; this.type = 'Unsupported'; this.kind = 'unsupported'; }
}
export class ThrowSignal { constructor(value, line) { this.value = value; this.line = line; } }

// ---------------------------------------------------------------- keys / equality / order
export function keyOf(v) {
  if (v === null || v === undefined) return 'z';
  switch (typeof v) {
    case 'number': return `n${v}`;
    case 'bigint': return `n${v}`;
    case 'string': return `s${v}`;
    case 'boolean': return v ? 'T' : 'F';
    default: break;
  }
  if (v instanceof Chr) return `c${v.c}`;
  if (v instanceof Dbl) return `d${v.v}`;
  if (v instanceof Pair) return `p(${keyOf(v.first)},${keyOf(v.second)})`;
  if (v instanceof Tup) return `t(${v.items.map(keyOf).join(',')})`;
  if (Array.isArray(v)) return `[${v.map(keyOf).join(',')}]`;
  if (v instanceof Obj) return `o${v.id}`;
  if (v instanceof SetObj) return `S{${v.keys().map(keyOf).join(',')}}`;
  return `?${String(v)}`;
}

const num = (x) => (x instanceof Chr ? x.c : x instanceof Dbl ? x.v : typeof x === 'boolean' ? (x ? 1 : 0) : x);

export function compare(a, b) {
  if (a instanceof Pair && b instanceof Pair) { const c = compare(a.first, b.first); return c || compare(a.second, b.second); }
  if (a instanceof Tup && b instanceof Tup) { for (let i = 0; i < a.items.length; i++) { const c = compare(a.items[i], b.items[i]); if (c) return c; } return 0; }
  if (Array.isArray(a) && Array.isArray(b)) {
    const n = Math.min(a.length, b.length);
    for (let i = 0; i < n; i++) { const c = compare(a[i], b[i]); if (c) return c; }
    return a.length - b.length;
  }
  if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
  const x = num(a), y = num(b);
  return x < y ? -1 : x > y ? 1 : 0;
}

export function equals(a, b) {
  if (a === b) return true;
  if (a === null || b === null || a === undefined || b === undefined) return false;
  if (typeof a === 'object' || typeof b === 'object') {
    if (a instanceof Chr || b instanceof Chr || a instanceof Dbl || b instanceof Dbl) return num(a) === num(b);
    if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((x, i) => equals(x, b[i]));
    if (a instanceof Pair && b instanceof Pair) return equals(a.first, b.first) && equals(a.second, b.second);
    if (a instanceof Tup && b instanceof Tup) return a.items.length === b.items.length && a.items.every((x, i) => equals(x, b.items[i]));
    return false;
  }
  if (typeof a === 'bigint' || typeof b === 'bigint') return BigInt(a) === BigInt(b);
  return num(a) === num(b);
}

// ---------------------------------------------------------------- copying (C++ value semantics)
export function cloneVal(v) {
  if (v === null || typeof v !== 'object') return v;
  if (Array.isArray(v)) { const a = v.map(cloneVal); if (v.et) a.et = v.et; return a; }
  if (v instanceof Pair) return new Pair(cloneVal(v.first), cloneVal(v.second));
  if (v instanceof Tup) return new Tup(v.items.map(cloneVal));
  if (v instanceof MapObj) { const m = new MapObj(v.kind, v.ordered, v.cmp); m.kt = v.kt; m.vt = v.vt; m.jhash = v.jhash; m.cap = v.cap; for (const [k, e] of v.m) m.m.set(k, new Pair(cloneVal(e.first), cloneVal(e.second))); return m; }
  if (v instanceof SetObj) { const m = new SetObj(v.kind, v.ordered, v.cmp); m.kt = v.kt; m.jhash = v.jhash; m.cap = v.cap; for (const [k, e] of v.m) m.m.set(k, cloneVal(e)); return m; }
  if (v instanceof Seq) { const s = new Seq(v.kind, v.cmp); s.et = v.et; s.a = v.a.map(cloneVal); return s; }
  if (v instanceof StrBuilder) return new StrBuilder(v.s);
  return v; // Obj (pointers), lambdas, chars, doubles: shared / immutable
}

/** Copy of a struct instance used by value. */
export function cloneObj(o) {
  const f = {};
  for (const [k, v] of Object.entries(o.f)) f[k] = cloneVal(v);
  return new Obj(o.cls, f);
}

// ---------------------------------------------------------------- snapshots (JSON-safe)
const CAP = 120;
const BIG = (x) => (x >= BigInt(Number.MIN_SAFE_INTEGER) && x <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(x) : x.toString());

/**
 * Snapshot a runtime value for the trace. Node-like objects (val + next / left / right) go to `heap` and are
 * referenced by id so the UI can draw the whole list / tree.
 */
export function snap(v, heap, depth = 0, seen = null) {
  if (v === null || v === undefined) return null;
  switch (typeof v) {
    case 'number': return Number.isFinite(v) ? v : String(v);
    case 'bigint': return BIG(v);
    case 'boolean': return v;
    case 'string': return v.length > 200 ? `${v.slice(0, 200)}…` : v;
    default: break;
  }
  if (v instanceof Chr) return { $: 'chr', s: v.s };
  if (v instanceof Dbl) return Number.isFinite(v.v) ? (Number.isInteger(v.v) ? { $: 'dbl', v: v.v } : v.v) : String(v.v);
  if (v instanceof Uninit) return { $: 'uninit' };
  if (depth > 6) return { $: 'unk', s: '…' };
  if (Array.isArray(v)) {
    if (seen && seen.has(v)) return { $: 'cycle' };
    const out = [];
    const s2 = seen ? new Set(seen).add(v) : new Set([v]);
    for (let i = 0; i < v.length && i < CAP; i++) out.push(snap(v[i], heap, depth + 1, s2));
    return v.length > CAP ? { $: 'trunc', n: v.length, e: out } : out;
  }
  if (v instanceof Pair) return { $: 'tuple', e: [snap(v.first, heap, depth + 1, seen), snap(v.second, heap, depth + 1, seen)] };
  if (v instanceof Tup) return { $: 'tuple', e: v.items.map((x) => snap(x, heap, depth + 1, seen)) };
  if (v instanceof MapObj) { const es = v.entries(); return { $: 'map', e: es.slice(0, CAP).map((e) => [snap(e.first, heap, depth + 1, seen), snap(e.second, heap, depth + 1, seen)]), n: es.length }; }
  if (v instanceof SetObj) { const ks = v.keys(); return { $: 'set', e: ks.slice(0, CAP).map((k) => snap(k, heap, depth + 1, seen)), n: ks.length }; }
  if (v instanceof Seq) return { $: v.kind === 'stack' || v.kind === 'queue' || v.kind === 'deque' || v.kind === 'pq' ? v.kind : 'deque', e: v.a.slice(0, CAP).map((x) => snap(x, heap, depth + 1, seen)), n: v.a.length };
  if (v instanceof StrBuilder) return v.s;
  if (v instanceof Obj) {
    const nodeKind = nodeKindOf(v);
    if (nodeKind) {
      const a = `n${v.id}`;
      if (!(a in heap) && Object.keys(heap).length < 400) {
        heap[a] = { k: nodeKind };
        const rec = heap[a];
        rec.val = snap(v.f.val ?? v.f.data ?? v.f.key ?? null, heap, depth + 1, seen);
        for (const nm of ['next', 'left', 'right']) if (nm in v.f) { const t = v.f[nm]; rec[nm] = t instanceof Obj ? `n${t.id}` : null; if (t instanceof Obj) snap(t, heap, depth + 1, seen); }
      }
      return { $: 'ref', a, k: nodeKind };
    }
    if (seen && seen.has(v)) return { $: 'cycle' };
    const s2 = seen ? new Set(seen).add(v) : new Set([v]);
    const f = {};
    let n = 0;
    for (const [k, x] of Object.entries(v.f)) { if (n++ >= 20) break; f[k] = snap(x, heap, depth + 1, s2); }
    return { $: 'obj', t: v.cls.name, f };
  }
  if (v instanceof Iter) return { $: 'unk', s: 'iterator' };
  return { $: 'unk', s: v.constructor ? v.constructor.name : 'value' };
}

function nodeKindOf(o) {
  const f = o.f;
  const has = (n) => n in f;
  if ((has('val') || has('data') || has('key')) && (has('left') || has('right'))) return 'TreeNode';
  if ((has('val') || has('data')) && has('next') && !has('left')) return 'ListNode';
  return null;
}

/** Plain JSON form of a value for results (TreeNode / ListNode become LeetCode arrays). */
export function toPlain(v, depth = 0) {
  if (v === null || v === undefined) return null;
  if (depth > 12) return null;
  switch (typeof v) {
    case 'number': return Number.isFinite(v) ? v : String(v);
    case 'bigint': return BIG(v);
    case 'boolean': case 'string': return v;
    default: break;
  }
  if (v instanceof Chr) return v.s;
  if (v instanceof Dbl) return v.v;
  if (v instanceof Uninit) return null;
  if (Array.isArray(v)) return v.map((x) => toPlain(x, depth + 1));
  if (v instanceof Pair) return [toPlain(v.first, depth + 1), toPlain(v.second, depth + 1)];
  if (v instanceof Tup) return v.items.map((x) => toPlain(x, depth + 1));
  if (v instanceof MapObj) return Object.fromEntries(v.entries().map((e) => [String(toPlain(e.first)), toPlain(e.second, depth + 1)]));
  if (v instanceof SetObj) return v.keys().map((k) => toPlain(k, depth + 1));
  if (v instanceof Seq) return v.a.map((x) => toPlain(x, depth + 1));
  if (v instanceof StrBuilder) return v.s;
  if (v instanceof Obj) {
    const k = nodeKindOf(v);
    if (k === 'ListNode') { const out = []; let n = v; let guard = 0; while (n instanceof Obj && guard++ < 10000) { out.push(toPlain(n.f.val ?? n.f.data, depth + 1)); n = n.f.next; } return out; }
    if (k === 'TreeNode') {
      const out = [];
      const q = [v];
      while (q.length) { const n = q.shift(); if (!(n instanceof Obj)) { out.push(null); continue; } out.push(toPlain(n.f.val ?? n.f.data ?? n.f.key, depth + 1)); q.push(n.f.left ?? null, n.f.right ?? null); if (out.length > 5000) break; }
      while (out.length && out[out.length - 1] === null) out.pop();
      return out;
    }
    return Object.fromEntries(Object.entries(v.f).map(([k2, x]) => [k2, toPlain(x, depth + 1)]));
  }
  return null;
}
