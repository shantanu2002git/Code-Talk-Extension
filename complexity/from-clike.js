// C++ / Java AST (src/engine/clike/parser.js) -> language-neutral IR used by the complexity analyzer.
import { parse } from '../engine/clike/parser.js';

const HASHMAP = new Set(['unordered_map', 'HashMap', 'Map', 'Hashtable', 'LinkedHashMap', 'unordered_multimap', 'ConcurrentHashMap']);
const TREEMAP = new Set(['map', 'TreeMap', 'SortedMap', 'NavigableMap', 'multimap']);
const HASHSET = new Set(['unordered_set', 'HashSet', 'Set', 'LinkedHashSet', 'unordered_multiset']);
const TREESET = new Set(['set', 'TreeSet', 'SortedSet', 'NavigableSet', 'multiset']);
const LIST = new Set(['vector', 'ArrayList', 'List', 'Vector', 'list_', 'array', 'Collection', 'Iterable']);
const LINKED = new Set(['list', 'LinkedList']);
const INTS = new Set(['int', 'long', 'short', 'uint', 'ulong', 'uchar', 'char', 'Integer', 'Long', 'Character', 'Short', 'Byte', 'byte', 'size_t']);
const FLOATS = new Set(['double', 'float', 'Double', 'Float']);

export function convType(ty, ctx = {}) {
  if (!ty) return { k: 'unknown' };
  if (ty.k !== 'type') return { k: 'unknown' };
  let base = convBase(ty, ctx);
  let dims = (ty.dims || 0) + (ty.arr ? ty.arr.length : 0);
  if (ty.ptr && !ctx.classKind) { /* pointer to a user class handled in convBase */ }
  while (dims-- > 0) base = { k: 'array', e: base };
  return base;
}
function convBase(ty, ctx) {
  const n = ty.name;
  if (n === 'auto' || n === 'var') return { k: 'unknown', auto: true };
  if (INTS.has(n)) return { k: 'int', name: n };
  if (FLOATS.has(n)) return { k: 'float' };
  if (n === 'bool' || n === 'Boolean') return { k: 'bool' };
  if (n === 'string' || n === 'String') return { k: 'str' };
  if (n === 'StringBuilder' || n === 'StringBuffer') return { k: 'sb' };
  if (n === 'void') return { k: 'void' };
  const a0 = ty.args && ty.args[0] ? convType(ty.args[0], ctx) : { k: 'unknown' };
  const a1 = ty.args && ty.args[1] ? convType(ty.args[1], ctx) : { k: 'unknown' };
  if (HASHMAP.has(n)) return { k: 'map', key: a0, e: a1 };
  if (TREEMAP.has(n)) return { k: 'sortedmap', key: a0, e: a1 };
  if (HASHSET.has(n)) return { k: 'set', e: a0 };
  if (TREESET.has(n)) return { k: 'sortedset', e: a0 };
  if (LIST.has(n)) return { k: 'list', e: a0, impl: n === 'List' || n === 'Collection' || n === 'Iterable' ? 'List(assumed ArrayList)' : n };
  if (LINKED.has(n)) return { k: 'linked', e: a0 };
  if (n === 'stack' || n === 'Stack') return { k: 'stack', e: a0 };
  if (n === 'queue' || n === 'Queue') return { k: 'queue', e: a0 };
  if (n === 'deque' || n === 'Deque' || n === 'ArrayDeque') return { k: 'deque', e: a0 };
  if (n === 'priority_queue' || n === 'PriorityQueue') return { k: 'heap', e: a0 };
  if (n === 'pair' || n === 'tuple' || n === 'Pair' || n === 'Map.Entry' || n === 'Entry') return { k: 'tuple' };
  if (ctx.classes && ctx.classes[n]) return { k: ctx.classes[n], cls: n };
  return { k: 'obj', cls: n };
}

class Conv {
  constructor(lang, ast) {
    this.lang = lang;
    this.classKinds = {};
    this.funcs = [];
    this.walkClasses(ast);
  }
  walkClasses(node) {
    const visit = (c) => {
      if (!c || c.k !== 'class') return;
      const names = new Set((c.fields || []).filter((f) => f.k === 'field').map((f) => f.name));
      if (names.has('left') || names.has('right')) this.classKinds[c.name] = 'tree';
      else if (names.has('next')) this.classKinds[c.name] = 'node';
      else if (names.has('children') || names.has('neighbors')) this.classKinds[c.name] = 'nary';
      (c.inner || []).forEach(visit);
    };
    (node.items || node.decls || node.body || []).forEach(visit);
    for (const c of this.allClasses(node)) visit(c);
  }
  allClasses(node) { return Array.isArray(node.classes) ? node.classes : []; }
  T(ty) { return convType(ty, { classes: this.classKinds }); }

  // ---------------------------------------------------------------- expressions
  E(n) {
    if (!n) return { t: 'unk' };
    switch (n.k) {
      case 'num': return { t: 'num', v: Number(String(n.value).replace(/[lLfFuU]+$/, '')) };
      case 'bool': return { t: 'num', v: n.value ? 1 : 0, bool: true };
      case 'chr': return { t: 'num', v: typeof n.value === 'string' ? n.value.charCodeAt(0) : Number(n.value) || 0, chr: true };
      case 'str': return { t: 'lit', kind: 'str', a: [], len: String(n.value).length, s: String(n.value) };
      case 'null': return { t: 'null' };
      case 'id': return { t: 'id', n: n.name };
      case 'this': return { t: 'id', n: 'this' };
      case 'paren': return this.E(n.expr);
      case 'cast': return this.E(n.expr);
      case 'deref': return this.E(n.expr);
      case 'addr': return this.E(n.expr);
      case 'comma': return { t: 'op', o: ',', a: (n.exprs || [n.left, n.right]).filter(Boolean).map((x) => this.E(x)) };
      case 'bin': return { t: 'op', o: n.op, a: [this.E(n.left), this.E(n.right)] };
      case 'unary': return { t: 'op', o: n.op === '-' ? 'neg' : n.op, a: [this.E(n.expr)] };
      case 'cond': return { t: 'op', o: '?:', a: [this.E(n.cond), this.E(n.a), this.E(n.b)] };
      case 'preinc': case 'postinc': return { t: 'incdec', op: n.op, target: this.E(n.expr), post: n.k === 'postinc' };
      case 'assign': return { t: 'assign', op: n.op, target: this.E(n.target), v: this.E(n.value) };
      case 'index': return { t: 'idx', o: this.E(n.obj), i: this.E(n.index) };
      case 'member': return { t: 'attr', o: this.E(n.obj), n: n.name };
      case 'scope': return { t: 'id', n: `${n.left && n.left.name ? n.left.name + '::' : ''}${n.name}` };
      case 'call': return this.call(n);
      case 'new': return { t: 'new', ty: this.T(n.type), a: (n.args || []).map((x) => this.E(x)), cls: n.type && n.type.name, line: n.line };
      case 'construct': return { t: 'new', ty: this.T(n.type), a: (n.args || []).map((x) => this.E(x)), cls: n.type && n.type.name, brace: n.brace, line: n.line };
      case 'ctorcall': return { t: 'new', ty: { k: 'unknown' }, a: (n.args || []).map((x) => this.E(x)), brace: n.brace, ctor: true };
      case 'newarr': {
        let ty = this.T(n.type);
        const dimsN = (n.dims || []).length + (n.extra || 0);
        for (let i = 0; i < dimsN; i++) ty = { k: 'array', e: ty };
        return { t: 'new', ty, alloc: true, a: (n.dims || []).map((x) => this.E(x)), init: n.init ? this.E(n.init) : null, line: n.line };
      }
      case 'initlist': return { t: 'lit', kind: 'list', a: (n.items || []).map((x) => this.E(x)) };
      case 'lambda': return { t: 'lambda', body: this.S(n.body) };
      case 'sizeof': return { t: 'num', v: 1 };
      case 'typeexpr': return { t: 'unk' };
      default: return { t: 'unk', note: n.k };
    }
  }
  call(n) {
    const c = n.callee;
    const a = (n.args || []).map((x) => this.E(x));
    if (c.k === 'id') return { t: 'call', fn: c.name, a, line: n.line };
    if (c.k === 'scope') { const left = c.left && c.left.name ? c.left.name : ''; return { t: 'call', fn: left ? `${left}.${c.name}` : c.name, a, line: n.line }; }
    if (c.k === 'member') {
      const o = c.obj;
      if (o && o.k === 'id' && /^[A-Z]/.test(o.name) && !this.isVar(o.name)) return { t: 'call', fn: `${o.name}.${c.name}`, a, line: n.line };
      return { t: 'call', recv: this.E(o), m: c.name, a, line: n.line };
    }
    return { t: 'call', fn: '?', a, line: n.line, dynamic: true };
  }
  isVar() { return false; }

  // ---------------------------------------------------------------- statements
  S(n) {
    if (!n) return [];
    switch (n.k) {
      case 'block': return n.stmts.flatMap((x) => this.S(x));
      case 'empty': return [];
      case 'decl': return n.decls.map((d) => {
        const ty = this.T(d.type);
        let init = d.init ? this.E(d.init) : null;
        if (d.type && d.type.arr && d.type.arr.length) init = { t: 'new', ty, alloc: true, a: d.type.arr.filter(Boolean).map((x) => this.E(x)), init };
        if (init && init.ctor) init = { ...init, ty };
        return { s: 'decl', n: d.name, ty, init, line: d.line || n.line, ref: Boolean(d.type && d.type.ref) };
      });
      case 'bind': return [{ s: 'decl', n: (n.names || []).join(','), ty: { k: 'tuple' }, init: this.E(n.init), line: n.line }];
      case 'expr': return [this.exprStmt(n.expr, n.line)];
      case 'if': return [{ s: 'if', cond: this.E(n.cond), then: this.S(n.then), else: this.S(n.else), line: n.line }];
      case 'while': return [{ s: 'while', cond: this.E(n.cond), body: this.S(n.body), line: n.line }];
      case 'dowhile': return [{ s: 'while', cond: this.E(n.cond), body: this.S(n.body), line: n.line, doWhile: true }];
      case 'for': return [{ s: 'for', mode: 'c', init: n.init ? this.S(n.init) : [], cond: n.cond ? this.E(n.cond) : null, update: n.update ? [this.exprStmt(n.update, n.line)] : [], body: this.S(n.body), line: n.line }];
      case 'foreach': return [{ s: 'for', mode: 'each', vars: n.names || [n.name], ty: n.type ? this.T(n.type) : null, iter: this.E(n.coll), body: this.S(n.body), line: n.line }];
      case 'return': return [{ s: 'return', v: n.expr ? this.E(n.expr) : null, line: n.line }];
      case 'break': return [{ s: 'break', line: n.line }];
      case 'continue': return [{ s: 'continue', line: n.line }];
      case 'throw': return [{ s: 'throw', line: n.line }];
      case 'switch': return [{ s: 'switch', disc: this.E(n.disc), cases: n.cases.map((c) => c.body.flatMap((x) => this.S(x))), line: n.line }];
      case 'try': return [{ s: 'try', body: this.S(n.body), handlers: (n.catches || []).map((c) => this.S(c.body)), fin: this.S(n.fin), line: n.line }];
      case 'localClass': case 'typedefStmt': case 'typedef': return [];
      default: return [{ s: 'expr', e: { t: 'unk', note: n.k }, line: n.line }];
    }
  }
  exprStmt(e, line) { return { s: 'expr', e: this.E(e), line }; }

  func(f, cls) {
    return { name: f.name, cls: cls ? cls.name : f.cls || null, line: f.line, endLine: f.endLine, isCtor: f.isCtor, isStatic: f.isStatic, access: f.access,
      params: f.params.map((p) => ({ n: p.name, ty: this.T(p.type), ref: Boolean(p.type && p.type.ref), isConst: Boolean(p.type && p.type.isConst) })), body: this.S(f.body), ret: this.T(f.ret), decorators: [] };
  }
}

export function clikeToIR(lang, code) {
  const ast = parse(code, lang);
  const conv = new Conv(lang, ast);
  const funcs = [];
  const classes = {};
  const visit = (c) => {
    if (!c || c.k !== 'class') return;
    const fields = (c.fields || []).filter((f) => f.k === 'field');
    classes[c.name] = { name: c.name, fields: fields.map((f) => ({ n: f.name, ty: conv.T(f.type) })) };
    for (const m of c.methods || []) funcs.push(conv.func(m, c));
    for (const m of c.ctors || []) funcs.push(conv.func(m, c));
    (c.inner || []).forEach(visit);
  };
  const top = ast.items || ast.decls || ast.body || [];
  for (const item of top) {
    if (!item) continue;
    if (item.k === 'class') visit(item);
    else if (item.k === 'func') funcs.push(conv.func(item, null));
  }
  // global functions may be stored separately
  for (const f of ast.funcs || []) if (!funcs.some((x) => x.name === f.name && x.line === f.line)) funcs.push(conv.func(f, null));
  for (const c of ast.classes || []) if (!classes[c.name]) visit(c);
  // member field kinds of user classes (so `root.left` is understood as a tree child)
  return { lang, funcs, classes, classKinds: conv.classKinds };
}
