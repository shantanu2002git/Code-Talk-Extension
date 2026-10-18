// Public entry point of the C++ / Java engine: parse -> run the entry function -> trace.
import { Interpreter, BudgetError } from './interp.js';
import { ParseError } from './parser.js';
import * as V from './values.js';

const { Dbl, Chr, Pair, Tup, Obj, MapObj, SetObj, RuntimeError, Unsupported, ThrowSignal, toPlain, snap } = V;

const VAL_NAMES = ['val', 'data', 'key', 'value', 'info', 'x'];

function walkAst(node, fn) {
  if (!node || typeof node !== 'object') return;
  if (Array.isArray(node)) { for (const x of node) walkAst(x, fn); return; }
  if (node.k) fn(node);
  for (const k of Object.keys(node)) { const v = node[k]; if (v && typeof v === 'object') walkAst(v, fn); }
}

/** List the functions a user could mean as "the solution", best guess first. */
export function detectEntries(lang, code) {
  const it = new Interpreter({ lang });
  it.load(code);
  const funcs = [];
  for (const c of Object.values(it.classes)) { if (c.prelude) continue; for (const m of c.methods) funcs.push({ fn: m, cls: c.name }); }
  for (const list of Object.values(it.funcs)) for (const f of list) if (!f.noTrace) funcs.push({ fn: f, cls: null });
  const called = new Map();
  for (const { fn, cls } of funcs) {
    walkAst(fn.body, (n) => {
      if (n.k === 'call') {
        const c = n.callee;
        const nm = c.k === 'id' ? c.name : c.k === 'member' ? c.name : c.k === 'scope' ? c.name : null;
        if (nm) called.set(nm, (called.get(nm) || new Set()).add(fn.name));
      }
    });
    void cls;
  }
  const cands = funcs.filter(({ fn }) => fn.name !== 'main' && !fn.name.startsWith('operator'));
  const score = (x) => {
    let s = 0;
    const callers = [...(called.get(x.fn.name) || [])].filter((n) => n !== x.fn.name);
    if (!callers.length) s += 10;
    if (x.cls === 'Solution') s += 5;
    if (x.fn.access === 'public') s += 2;
    if (!x.fn.isStatic || lang === 'java') s += 1;
    s -= x.fn.line / 10000;
    return s;
  };
  cands.sort((a, b) => score(b) - score(a));
  const main = funcs.find(({ fn }) => fn.name === 'main');
  return {
    candidates: cands.map(({ fn, cls }) => ({ name: fn.name, cls, params: fn.params.map((p) => ({ name: p.name, type: typeStr(p.type) })), ret: fn.ret ? typeStr(fn.ret) : 'void', line: fn.line, endLine: fn.endLine })),
    main: main ? { name: 'main', line: main.fn.line } : null,
  };
}

export function typeStr(t) {
  if (!t) return '';
  let s = t.name;
  if (t.args && t.args.length) s += `<${t.args.map((a) => (a.k === 'num' ? a.value : typeStr(a))).join(',')}>`;
  s += '*'.repeat(t.ptr || 0);
  s += '[]'.repeat(t.dims || 0);
  if (t.arr) s += t.arr.map(() => '[]').join('');
  if (t.ref) s += '&';
  return s;
}

// ---------------------------------------------------------------- JSON -> runtime values
function bareObj(it, cls) {
  const o = new Obj(cls, {});
  o.types = {};
  for (const k of it.allFields(cls)) for (const f of k.fields) if (f.k === 'field' && !f.static) { const ty = it.resolveType(f.type); o.f[f.name] = it.defaultValue(ty); o.types[f.name] = ty; }
  return o;
}

function fieldNames(it, cls) {
  const names = [];
  for (const k of it.allFields(cls)) for (const f of k.fields) if (f.k === 'field' && !f.static) names.push(f.name);
  return names;
}

function buildTree(it, cls, arr) {
  if (!arr || !arr.length || arr[0] === null) return null;
  const names = fieldNames(it, cls);
  const vn = VAL_NAMES.find((n) => names.includes(n)) || names[0];
  const mk = (v) => { const o = bareObj(it, cls); o.f[vn] = it.coerce(typeof v === 'number' ? v : Number(v), o.types[vn]); if (it.lang === 'cpp') o.heap = true; return o; };
  const root = mk(arr[0]);
  const q = [root];
  let i = 1;
  while (q.length && i < arr.length) {
    const n = q.shift();
    if (i < arr.length && arr[i] !== null) { n.f.left = mk(arr[i]); q.push(n.f.left); }
    i++;
    if (i < arr.length && arr[i] !== null) { n.f.right = mk(arr[i]); q.push(n.f.right); }
    i++;
  }
  return root;
}

function buildList(it, cls, arr) {
  if (!arr || !arr.length) return null;
  const names = fieldNames(it, cls);
  const vn = VAL_NAMES.find((n) => names.includes(n)) || names[0];
  let head = null, tail = null;
  for (const v of arr) {
    const o = bareObj(it, cls);
    o.f[vn] = it.coerce(Number(v), o.types[vn]);
    if (it.lang === 'cpp') o.heap = true;
    if (!head) head = o; else tail.f.next = o;
    tail = o;
  }
  return head;
}

export function fromJson(it, v, ty) {
  ty = it.resolveType(ty);
  const n = ty.name;
  if (ty.ptr || it.isUserClass(n)) {
    if (it.isUserClass(n)) {
      const cls = it.classes[n];
      const names = fieldNames(it, cls);
      if (names.includes('left') || names.includes('right')) return v === null ? null : buildTree(it, cls, v);
      if (names.includes('next')) return v === null ? null : buildList(it, cls, v);
      if (Array.isArray(v)) return it.instantiate(cls, v.map((x) => x), 1);
      return v === null ? null : it.instantiate(cls, [v], 1);
    }
    if (ty.ptr && Array.isArray(v)) { const a = v.map((x) => fromJson(it, x, { ...ty, ptr: ty.ptr - 1 })); a.et = { ...ty, ptr: ty.ptr - 1 }; return a; }
  }
  if (ty.dims) { const et = { ...ty, dims: ty.dims - 1 }; const a = (v || []).map((x) => fromJson(it, x, et)); a.et = et; return a; }
  if (ty.arr) { const et = { ...ty, arr: ty.arr.slice(1).length ? ty.arr.slice(1) : null }; const a = (v || []).map((x) => fromJson(it, x, et)); a.et = et; return a; }
  switch (n) {
    case 'int': case 'short': case 'uint': case 'Integer': case 'ulong': return it.coerce(typeof v === 'string' ? Number(v) : v, ty);
    case 'long': case 'Long': return BigInt(v);
    case 'double': case 'Double': return new Dbl(Number(v));
    case 'bool': case 'Boolean': return v === true || v === 'true';
    case 'char': case 'Character': case 'uchar': return typeof v === 'string' ? Chr.from(v) : Chr.of(v);
    case 'string': return v === null ? null : String(v);
    case 'pair': return new Pair(fromJson(it, v[0], ty.args[0]), fromJson(it, v[1], ty.args[1]));
    case 'tuple': return new Tup(v.map((x, i) => fromJson(it, x, ty.args[i])));
    case 'map': case 'unordered_map': case 'TreeMap': case 'HashMap': case 'Map': { const m = it.constructType(ty, [], 1); for (const [k, x] of Array.isArray(v) ? v : Object.entries(v)) it.mapPut(m, fromJson(it, k, ty.args[0]), fromJson(it, x, ty.args[1])); return m; }
    case 'set': case 'unordered_set': case 'TreeSet': case 'HashSet': case 'Set': { const s = it.constructType(ty, [], 1); for (const x of v) it.setAdd(s, fromJson(it, x, ty.args[0])); return s; }
    default: break;
  }
  if (Array.isArray(v)) {
    const et = ty.args && ty.args[0] ? it.resolveType(ty.args[0]) : null;
    const a = v.map((x) => (et ? fromJson(it, x, et) : fromJson(it, x, { k: 'type', name: 'auto', args: [], ptr: 0, ref: false, dims: 0 })));
    if (et) a.et = et;
    return a;
  }
  if (v === null || v === undefined) return null;
  if (typeof v === 'number') return Number.isInteger(v) ? v : new Dbl(v);
  return v;
}

function findNode(it, root, val) {
  const seen = new Set();
  const stack = [root];
  while (stack.length) {
    const n = stack.pop();
    if (!(n instanceof Obj) || seen.has(n)) continue;
    seen.add(n);
    const vn = VAL_NAMES.find((k) => k in n.f);
    if (vn && Number(n.f[vn]) === val) return n;
    for (const k of ['right', 'left', 'next']) if (n.f[k]) stack.push(n.f[k]);
  }
  return null;
}

function snapshotError(it, err) {
  const fr = it.frame;
  const heap = {};
  const vars = {};
  if (fr) it.collectVars(fr.env, vars, heap);
  return { i: it.steps.length, line: err.line || it.line, fn: fr ? fr.name : '', depth: fr ? fr.depth : 0, fid: fr ? fr.fid : 0, pfid: fr ? fr.pfid : -1, ev: 'error', vars, heap: Object.keys(heap).length ? heap : undefined, message: err.message };
}

/**
 * Run `code` and trace it.
 * opts: { lang, code, entry?, args (JSON array), maxSteps?, timeMs?, maxOps? }
 */
export function runClike(opts) {
  const lang = opts.lang === 'java' ? 'java' : 'cpp';
  const out = { ok: false, steps: [], stdout: '', warnings: [], truncated: false, result: undefined, error: null };
  const it = new Interpreter({ lang, maxSteps: opts.maxSteps || 3000, timeMs: opts.timeMs || 8000, maxOps: opts.maxOps || 15_000_000, maxDepth: opts.maxDepth });
  try {
    it.load(opts.code);
  } catch (e) {
    out.error = describeError(e, it);
    return out;
  }
  let fnName = opts.entry;
  let det = null;
  try { det = detectEntries(lang, opts.code); } catch (e) { det = { candidates: [], main: null }; }
  out.candidates = det.candidates;
  if (!fnName) {
    const argc = (opts.args || []).length;
    const fit = det.candidates.filter((c) => c.params.length === argc);
    fnName = fit.length ? fit[0].name : det.candidates.length ? det.candidates[0].name : det.main ? 'main' : null;
  }
  if (!fnName) { out.error = { type: 'NoEntry', message: 'Could not find a function to run in this code.', line: 1 }; return out; }
  out.entry = fnName;
  try {
    const cands = it.entryCandidates(fnName);
    if (!cands.length) throw new RuntimeError(`Function "${fnName}" was not found in the code`, 1);
    const args = opts.args || [];
    const fn = cands.find((c) => c.params.length === args.length) || cands[0];
    out.entrySig = { name: fn.name, params: fn.params.map((p) => ({ name: p.name, type: typeStr(p.type) })), ret: fn.ret ? typeStr(fn.ret) : 'void' };
    if (fn.params.length !== args.length) throw new RuntimeError(`"${fn.name}" takes ${fn.params.length} argument(s) but the input has ${args.length}`, fn.line);
    const rtArgs = fn.params.map((p, i) => fromJson(it, args[i], p.type));
    // node-pointer parameters given as plain values (LCA style: p = 5, q = 1) refer to nodes of the first tree / list
    rtArgs.forEach((a, i) => {
      const ty = it.resolveType(fn.params[i].type);
      if (i > 0 && ty.ptr && it.isUserClass(ty.name) && typeof args[i] === 'number') {
        const root = rtArgs.find((x, k) => k < i && x instanceof Obj);
        const found = root && findNode(it, root, args[i]);
        if (found) rtArgs[i] = found;
      }
    });
    it.entryArgs = rtArgs;
    const res = it.runEntry(fnName, rtArgs);
    out.ok = true;
    out.value = res.value;
    let rt = res.fn.ret && !(res.fn.ret.name === 'void' && !res.fn.ret.ptr) ? toPlain(res.value) : undefined;
    if (rt === null && res.fn.ret && res.fn.ret.ptr && it.isUserClass(res.fn.ret.name)) rt = [];
    out.result = rt;
    out.argsAfter = rtArgs.map((a) => toPlain(a));
  } catch (e) {
    out.error = describeError(e, it);
    if (!(e instanceof ParseError)) { const st = snapshotError(it, out.error); if (it.steps.length < it.maxSteps + 1) it.steps.push(st); }
  }
  out.steps = it.steps;
  out.stdout = it.stdout + (it.pendingOut && !it.stdout.endsWith(it.pendingOut) ? '' : '');
  out.warnings = it.warnings;
  out.truncated = it.truncated;
  out.totalCalls = it.fidc + 1;
  out.ops = it.ops;
  return out;
}

export function describeError(e, it) {
  if (e instanceof ParseError) return { type: 'SyntaxError', message: e.message, line: e.line, kind: 'syntax' };
  if (e instanceof Unsupported) return { type: 'Unsupported', message: e.message, line: e.line, kind: 'unsupported' };
  if (e instanceof BudgetError) return { type: 'Limit', message: e.message, line: it ? it.line : 0, kind: 'limit' };
  if (e instanceof ThrowSignal) { const v = e.value; const nm = v instanceof Obj ? v.cls.name : 'exception'; const msg = v instanceof Obj && v.f.message !== undefined ? v.f.message : ''; return { type: nm, message: `Uncaught ${nm}${msg ? `: ${msg}` : ''}`, line: e.line || (it && it.line), kind: 'runtime' }; }
  if (e instanceof RuntimeError) return { type: e.exc || 'RuntimeError', message: e.message, line: e.line || (it && it.line), kind: 'runtime' };
  if (e instanceof RangeError && /call stack/i.test(e.message)) return { type: 'StackOverflow', message: 'Stack overflow: the recursion is too deep for the visualizer (a real program may also overflow if the recursion never stops).', line: it ? it.line : 0, kind: 'runtime' };
  return { type: 'InternalError', message: `Visualizer internal error: ${e && e.message}`, line: it ? it.line : 0, kind: 'internal', stack: e && e.stack };
}

export { snap, MapObj, SetObj };
