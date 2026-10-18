// Methods of built-in values: strings, vectors / lists, maps, sets, stacks / queues, StringBuilder, iterators...
import * as V from './values.js';

const {
  Dbl, Chr, Pair, Tup, Obj, UNINIT, Cell, ElemRef, FieldRef, FnRef, MapObj, SetObj, Seq, Iter, Lambda, StrBuilder,
  RuntimeError, Unsupported, keyOf, equals, cloneVal,
} = V;

const isRef = (x) => x instanceof Cell || x instanceof ElemRef || x instanceof FieldRef || (x && x.constructor && x.constructor.name === 'StrIdxRef');

export function installMethods(I) {
  const N = (x) => I.num(x);
  const err = (msg, line, exc) => { const e = new RuntimeError(msg, line); if (exc) { e.exc = exc; e.catchable = true; } return e; };
  const noSuch = (line) => err('NoSuchElementException', line, 'NoSuchElementException');
  const chs = (x) => (x instanceof Chr ? x.s : typeof x === 'string' ? x : String.fromCharCode(N(x)));

  // ------------------------------------------------------------ maps / sets
  I.mapEntry = function mapEntry(m, key, create) {
    if (m.kt) key = I.coerce(key, m.kt);
    const kk = keyOf(key);
    let e = m.m.get(kk);
    if (!e && create) { e = new Pair(key, m.vt ? I.defaultValue(m.vt) : (I.lang === 'java' ? null : 0)); m.m.set(kk, e); m.dirty(); if (m.jhash) m.grow(); }
    return e || null;
  };
  I.mapPut = function mapPut(m, key, val) {
    if (m.kt) key = I.coerce(key, m.kt);
    if (m.vt) val = I.coerce(val, m.vt);
    const kk = keyOf(key);
    if (m.multi) { m.seq = (m.seq || 0) + 1; m.m.set(`${kk}#${m.seq}`, new Pair(key, val)); m.dirty(); return null; }
    const e = m.m.get(kk);
    if (e) { const old = e.second; e.second = val; return old; }
    m.m.set(kk, new Pair(key, val)); m.dirty();
    if (m.jhash) m.grow();
    return null;
  };
  I.setAdd = function setAdd(s, v) {
    if (s.kt) v = I.coerce(v, s.kt);
    const kk = keyOf(v);
    if (s.multi) { s.seq = (s.seq || 0) + 1; s.m.set(`${kk}#${s.seq}`, v); s.dirty(); return true; }
    if (s.m.has(kk)) return false;
    s.m.set(kk, v); s.dirty();
    if (s.jhash) s.grow();
    return true;
  };
  const mapKeys = (m, key) => { const kk = keyOf(m.kt ? I.coerce(key, m.kt) : key); const out = []; for (const [k, e] of m.m) if (k === kk || k.startsWith(`${kk}#`)) out.push(k); return out; };
  const delKey = (c, key) => { let n = 0; for (const k of mapKeys(c, key)) { c.m.delete(k); n++; } if (n) c.dirty(); return n; };

  const entriesOf = (c) => (c instanceof MapObj ? c.entries() : c.keys());
  const elemOf = (c, it) => it.keys[it.pos];
  const mkIter = (c, pos) => { const ks = entriesOf(c); return new Iter(c, pos, ks); };
  const cmpOf = (c) => c.cmp || ((a, b) => I.cmpVals(a, b));
  const keyAt = (c, e) => (c instanceof MapObj ? e.first : e);

  // ------------------------------------------------------------ dispatcher
  I.callMethod = function callMethod(recv, name, args, ref, n) {
    const line = n.line;
    I.line = line;
    if (typeof recv === 'string') return stringMethod(recv, name, args, ref, n);
    if (Array.isArray(recv)) return arrayMethod(recv, name, args, ref, n);
    if (recv instanceof MapObj) return mapMethod(recv, name, args, ref, n);
    if (recv instanceof SetObj) return setMethod(recv, name, args, n);
    if (recv instanceof Seq) return seqMethod(recv, name, args, n);
    if (recv instanceof StrBuilder) return sbMethod(recv, name, args, n);
    if (recv instanceof Pair) return pairMethod(recv, name, args, n);
    if (recv instanceof Iter) return iterMethod(recv, name, args, n);
    if (recv && recv.isStream) { if (recv.java) return printMethod(recv, name, args, n); return recv; }
    if (recv instanceof Lambda || recv instanceof FnRef) return fnMethod(recv, name, args, n);
    if (recv instanceof V.Rng) return rngMethod(recv, name, args, n);
    if (typeof recv === 'number' || typeof recv === 'bigint' || recv instanceof Dbl || recv instanceof Chr || typeof recv === 'boolean') return boxedMethod(recv, name, args, n);
    if (recv instanceof Tup) { if (name === 'get') return recv.items[N(args[0])]; }
    if (recv && recv.$class) return I.callStaticBuiltin(recv.$class.name, name, { line, args: [], callee: null }, null);
    throw err(`Unknown method "${name}" on ${I.describe(recv)}`, line);
  };

  I.callObjectBuiltin = function callObjectBuiltin(o, name, args, line) {
    switch (name) {
      case 'getMessage': case 'what': case 'getLocalizedMessage': return o.f.message === undefined ? null : o.f.message;
      case 'toString': return I.str(o);
      case 'equals': return o === args[0];
      case 'hashCode': return V.javaHash(o);
      case 'name': return o.enumName;
      case 'ordinal': return o.f.ordinal;
      case 'compareTo': return o.f.ordinal - args[0].f.ordinal;
      case 'printStackTrace': return undefined;
      case 'getClass': return { $cls: o.cls.name, isStream: false };
      case 'getSimpleName': case 'getName': return o.cls.name;
      default: throw err(`${o.cls.name} has no method "${name}"`, line);
    }
  };

  function printMethod(s, name, args, n) {
    const f = (v) => I.str(v);
    switch (name) {
      case 'println': I.out(`${args.length ? (Array.isArray(args[0]) && args[0].et && args[0].et.name === 'char' ? args[0].map(chs).join('') : f(args[0])) : ''}\n`, s); return undefined;
      case 'print': I.out(Array.isArray(args[0]) && args[0].et && args[0].et.name === 'char' ? args[0].map(chs).join('') : f(args[0]), s); return undefined;
      case 'printf': case 'format': I.out(I.sprintf(args[0], args.slice(1), true), s); return s;
      case 'flush': case 'close': return undefined;
      case 'write': I.out(chs(args[0]), s); return undefined;
      default: throw err(`System.out.${name}() is not supported`, n.line);
    }
  }

  function rngMethod(r, name, args, n) {
    const next = () => { r.s = (Math.imul(r.s, 1103515245) + 12345) & 0x7fffffff; return r.s; };
    switch (name) {
      case 'nextInt': return args.length ? next() % N(args[0]) : next();
      case 'nextDouble': return new Dbl(next() / 2147483648);
      case 'nextBoolean': return (next() & 1) === 1;
      case 'nextLong': return BigInt(next());
      default: throw err(`Random.${name}() is not supported`, n.line);
    }
  }

  function boxedMethod(v, name, args, n) {
    switch (name) {
      case 'intValue': return I.wrap32(v);
      case 'longValue': return I.toLong(v);
      case 'doubleValue': return new Dbl(N(v));
      case 'charValue': case 'booleanValue': return v;
      case 'equals': return I.eq(v, args[0]) && typeof args[0] !== 'object' || (args[0] instanceof Chr && v instanceof Chr && v.c === args[0].c) || (args[0] instanceof Dbl && v instanceof Dbl && v.v === args[0].v);
      case 'compareTo': case 'compare': return I.cmpVals(v, args[0]);
      case 'hashCode': return V.javaHash(v);
      case 'toString': return I.str(v);
      case 'isNaN': return Number.isNaN(N(v));
      default: throw err(`Unknown method "${name}" on a number`, n.line);
    }
  }

  function pairMethod(p, name, args, n) {
    switch (name) {
      case 'getKey': case 'first': return p.first;
      case 'getValue': case 'second': return p.second;
      case 'setValue': { const o = p.second; p.second = args[0]; return o; }
      case 'equals': return equals(p, args[0]);
      case 'hashCode': return V.javaHash(p);
      case 'toString': return I.str(p);
      case 'swap': { const t = p.first; p.first = p.second; p.second = t; return undefined; }
      default: throw err(`pair has no method "${name}"`, n.line);
    }
  }

  function fnMethod(f, name, args, n) {
    switch (name) {
      case 'reversed': return new FnRef((x) => -I.makeCmp(f)(x[0], x[1]), 'reversed');
      case 'thenComparing': case 'thenComparingInt': case 'thenComparingLong': case 'thenComparingDouble': return new FnRef((x) => { const c = I.makeCmp(f)(x[0], x[1]); if (c) return c; const g = args[0]; const arity = g instanceof Lambda ? g.node.params.length : 2; if (arity === 1 || name !== 'thenComparing') return I.cmpVals(I.callValue(g, [x[0]]), I.callValue(g, [x[1]])); return I.makeCmp(g)(x[0], x[1]); }, 'then');
      case 'negate': return new FnRef((x) => !I.truthy(I.callValue(f, x)), 'negate');
      case 'andThen': return new FnRef((x) => I.callValue(args[0], [I.callValue(f, x)]), 'andThen');
      case 'compose': return new FnRef((x) => I.callValue(f, [I.callValue(args[0], x)]), 'compose');
      case 'equals': return f === args[0];
      default: return I.callValue(f, args, n.line);
    }
  }

  function iterMethod(it, name, args, n) {
    const len = () => (it.keys ? it.keys.length : Array.isArray(it.coll) ? it.coll.length : it.coll.a ? it.coll.a.length : 0);
    switch (name) {
      case 'hasNext': return it.pos < len();
      case 'next': { if (it.pos >= len()) throw noSuch(n.line); const e = it.keys ? it.keys[it.pos] : Array.isArray(it.coll) ? it.coll[it.pos] : it.coll.a[it.pos]; it.pos++; return e; }
      case 'remove': { const p = it.pos - 1; if (Array.isArray(it.coll)) { it.coll.splice(p, 1); it.pos--; } else if (it.coll instanceof SetObj) { const k = it.keys[p]; delKey(it.coll, k); it.keys = it.coll.keys(); it.pos--; } else if (it.coll instanceof MapObj) { const k = it.keys[p].first; delKey(it.coll, k); it.keys = it.coll.entries(); it.pos--; } else if (it.coll instanceof Seq) { it.coll.a.splice(p, 1); it.pos--; } return undefined; }
      default: throw err(`Iterator has no method "${name}"`, n.line);
    }
  }

  // ------------------------------------------------------------ strings
  const MUT = new Set(['push_back', 'pop_back', 'append', 'insert', 'erase', 'replace', 'clear', 'resize', 'assign', 'swap']);
  function strIdx(i, len, line) { if (i < 0 || i >= len) throw err(I.lang === 'java' ? `StringIndexOutOfBoundsException: index ${i}, length ${len}` : `out_of_range: string index ${i} is outside 0..${len - 1}`, line, I.lang === 'java' ? 'StringIndexOutOfBoundsException' : 'out_of_range'); }
  function strRange(a, b, len, line) { if (a < 0 || b > len || a > b) throw err(`StringIndexOutOfBoundsException: begin ${a}, end ${b}, length ${len}`, line, 'StringIndexOutOfBoundsException'); }

  function stringMethod(s, name, args, ref, n) {
    const line = n.line;
    const set = (v) => { if (ref && isRef(ref)) ref.set(v); };
    const java = I.lang === 'java';
    switch (name) {
      case 'size': case 'length': return s.length;
      case 'empty': case 'isEmpty': return s.length === 0;
      case 'isBlank': return s.trim().length === 0;
      case 'charAt': case 'at': { const i = N(args[0]); if (i < 0 || i >= s.length) throw err(java ? `StringIndexOutOfBoundsException: Index ${i} out of bounds for length ${s.length}` : `out_of_range: basic_string::at (index ${i} >= size ${s.length})`, line, java ? 'StringIndexOutOfBoundsException' : 'out_of_range'); return Chr.of(s.charCodeAt(i)); }
      case 'codePointAt': return s.charCodeAt(N(args[0]));
      case 'front': return Chr.of(s.charCodeAt(0));
      case 'back': return Chr.of(s.charCodeAt(s.length - 1));
      case 'substr': { const p = N(args[0]); if (p > s.length || p < 0) throw err(`out_of_range: substr position ${p} is past the end (size ${s.length})`, line, 'out_of_range'); const len = args.length > 1 ? N(args[1]) : -1; return len < 0 ? s.slice(p) : s.substr(p, len); }
      case 'substring': case 'subSequence': { const a = N(args[0]); const b = args.length > 1 ? N(args[1]) : s.length; strRange(a, b, s.length, line); return s.slice(a, b); }
      case 'find': { const p = args[1] !== undefined ? N(args[1]) : 0; if (p < 0) return -1; return s.indexOf(chs(args[0]), p); }
      case 'indexOf': { const p = args[1] !== undefined ? N(args[1]) : 0; return s.indexOf(chs(args[0]), p); }
      case 'rfind': case 'lastIndexOf': return args[1] !== undefined ? s.lastIndexOf(chs(args[0]), N(args[1])) : s.lastIndexOf(chs(args[0]));
      case 'find_first_of': { const set2 = chs(args[0]); if (args[1] !== undefined && N(args[1]) < 0) return -1; for (let i = args[1] ? N(args[1]) : 0; i < s.length; i++) if (set2.includes(s[i])) return i; return -1; }
      case 'find_last_of': { const set2 = chs(args[0]); for (let i = s.length - 1; i >= 0; i--) if (set2.includes(s[i])) return i; return -1; }
      case 'find_first_not_of': { const set2 = chs(args[0]); if (args[1] !== undefined && N(args[1]) < 0) return -1; for (let i = args[1] ? N(args[1]) : 0; i < s.length; i++) if (!set2.includes(s[i])) return i; return -1; }
      case 'contains': return s.includes(chs(args[0]));
      case 'startsWith': case 'starts_with': return args[1] !== undefined ? s.startsWith(chs(args[0]), N(args[1])) : s.startsWith(chs(args[0]));
      case 'endsWith': case 'ends_with': return s.endsWith(chs(args[0]));
      case 'equals': return typeof args[0] === 'string' && s === args[0];
      case 'equalsIgnoreCase': return typeof args[0] === 'string' && s.toLowerCase() === args[0].toLowerCase();
      case 'compareTo': { const o = args[0]; if (o === null) throw I.nullAccess('compareTo', line); if (java) { const m = Math.min(s.length, o.length); for (let i = 0; i < m; i++) if (s[i] !== o[i]) return s.charCodeAt(i) - o.charCodeAt(i); return s.length - o.length; } return s < o ? -1 : s > o ? 1 : 0; }
      case 'compare': return s < args[0] ? -1 : s > args[0] ? 1 : 0;
      case 'compareToIgnoreCase': { const a = s.toLowerCase(), b = args[0].toLowerCase(); return a < b ? -1 : a > b ? 1 : 0; }
      case 'hashCode': return V.javaHash(s);
      case 'toString': case 'c_str': case 'data': case 'intern': case 'strip': case 'trim': return name === 'trim' || name === 'strip' ? s.trim() : s;
      case 'toUpperCase': return s.toUpperCase();
      case 'toLowerCase': return s.toLowerCase();
      case 'concat': return s + args[0];
      case 'repeat': return s.repeat(N(args[0]));
      case 'replace': { if (java) { return s.split(chs(args[0])).join(chs(args[1])); } const p = N(args[0]), l = N(args[1]); const r = s.slice(0, p) + chs(args[2]) + s.slice(p + l); set(r); return r; }
      case 'replaceAll': return s.replace(new RegExp(args[0], 'g'), String(args[1]).replace(/\$(\d)/g, '$$$1'));
      case 'replaceFirst': return s.replace(new RegExp(args[0]), args[1]);
      case 'matches': return new RegExp(`^(?:${args[0]})$`).test(s);
      case 'split': { const lim = args[1] !== undefined ? N(args[1]) : 0; let parts = s.split(new RegExp(args[0])); if (lim > 0 && parts.length > lim) { const re = new RegExp(args[0], 'g'); parts = []; let last = 0, m; while (parts.length < lim - 1 && (m = re.exec(s))) { parts.push(s.slice(last, m.index)); last = m.index + m[0].length; if (m[0].length === 0) re.lastIndex++; } parts.push(s.slice(last)); } else if (lim === 0) while (parts.length && parts[parts.length - 1] === '') parts.pop(); if (parts.length && parts[0] === '' && s.length && new RegExp(`^(?:${args[0]})`).exec(s) && new RegExp(`^(?:${args[0]})`).exec(s)[0] === '') parts.shift(); parts.et = { k: 'type', name: 'string', args: [], ptr: 0, ref: false, dims: 0 }; return parts; }
      case 'toCharArray': { const a = [...s].map((c) => Chr.of(c.charCodeAt(0))); a.et = { k: 'type', name: 'char', args: [], ptr: 0, ref: false, dims: 0 }; return a; }
      case 'chars': throw new Unsupported('String.chars() streams are not supported', line);
      case 'begin': return new Iter(ref && isRef(ref) ? ref : new Cell(s, null), 0);
      case 'end': return new Iter(ref && isRef(ref) ? ref : new Cell(s, null), s.length);
      case 'rbegin': return new Iter(ref && isRef(ref) ? ref : new Cell(s, null), s.length - 1, null, true);
      case 'rend': return new Iter(ref && isRef(ref) ? ref : new Cell(s, null), -1, null, true);
      case 'capacity': return Math.max(15, s.length);
      case 'reserve': case 'shrink_to_fit': return undefined;
      case 'copy': return 0;
      case 'format': case 'formatted': return I.sprintf(s, args, true);
      case 'lines': case 'getBytes': throw new Unsupported(`String.${name}() is not supported`, line);
      default: break;
    }
    if (MUT.has(name)) {
      let r = s;
      switch (name) {
        case 'push_back': r = s + chs(args[0]); break;
        case 'pop_back': if (!s.length) throw err('pop_back() on an empty string', line); r = s.slice(0, -1); break;
        case 'append': r = args.length === 2 && typeof args[0] === 'number' ? s + chs(args[1]).repeat(args[0]) : s + chs(args[0]).slice(args.length >= 3 ? N(args[1]) : 0, args.length >= 3 ? N(args[1]) + N(args[2]) : undefined); break;
        case 'insert': { const p = N(args[0]); if (p > s.length) throw err('out_of_range: insert position past the end', line, 'out_of_range'); r = s.slice(0, p) + (args.length === 3 && typeof args[1] === 'number' ? chs(args[2]).repeat(args[1]) : chs(args[1])) + s.slice(p); break; }
        case 'erase': { if (args[0] instanceof Iter) { const a = args[0].pos; const b = args[1] instanceof Iter ? args[1].pos : a + 1; r = s.slice(0, a) + s.slice(b); } else { const p = args.length ? N(args[0]) : 0; r = args.length > 1 ? s.slice(0, p) + s.slice(p + N(args[1])) : s.slice(0, p); } break; }
        case 'clear': r = ''; break;
        case 'resize': { const k = N(args[0]); r = k <= s.length ? s.slice(0, k) : s + (args[1] ? chs(args[1]) : '\0').repeat(k - s.length); break; }
        case 'assign': r = args.length === 2 && typeof args[0] === 'number' ? chs(args[1]).repeat(args[0]) : chs(args[0]); break;
        case 'swap': { const o = args[0]; if (isRef(o)) { const t = o.get(); o.set(s); r = t; } break; }
        default: break;
      }
      set(r);
      return undefined;
    }
    throw err(`Unknown string method "${name}"`, line);
  }

  function sbMethod(sb, name, args, n) {
    const line = n.line;
    switch (name) {
      case 'append': sb.s += args[0] instanceof Chr ? args[0].s : Array.isArray(args[0]) ? args[0].map(chs).join('') : I.str(args[0]); return sb;
      case 'toString': return sb.s;
      case 'length': return sb.s.length;
      case 'isEmpty': return sb.s.length === 0;
      case 'charAt': { const i = N(args[0]); strIdx(i, sb.s.length, line); return Chr.of(sb.s.charCodeAt(i)); }
      case 'reverse': sb.s = [...sb.s].reverse().join(''); return sb;
      case 'insert': { const p = N(args[0]); strRange(p, p, sb.s.length, line); sb.s = sb.s.slice(0, p) + I.str(args[1]) + sb.s.slice(p); return sb; }
      case 'deleteCharAt': { const i = N(args[0]); strIdx(i, sb.s.length, line); sb.s = sb.s.slice(0, i) + sb.s.slice(i + 1); return sb; }
      case 'delete': { const a = N(args[0]); const b = Math.min(N(args[1]), sb.s.length); strRange(a, b, sb.s.length, line); sb.s = sb.s.slice(0, a) + sb.s.slice(b); return sb; }
      case 'setCharAt': { const i = N(args[0]); strIdx(i, sb.s.length, line); sb.s = sb.s.slice(0, i) + chs(args[1]) + sb.s.slice(i + 1); return undefined; }
      case 'setLength': { const k = N(args[0]); sb.s = k <= sb.s.length ? sb.s.slice(0, k) : sb.s + '\0'.repeat(k - sb.s.length); return undefined; }
      case 'indexOf': return sb.s.indexOf(args[0]);
      case 'lastIndexOf': return sb.s.lastIndexOf(args[0]);
      case 'substring': return sb.s.slice(N(args[0]), args.length > 1 ? N(args[1]) : undefined);
      case 'replace': sb.s = sb.s.slice(0, N(args[0])) + args[2] + sb.s.slice(N(args[1])); return sb;
      case 'equals': return sb === args[0];
      case 'compareTo': return sb.s < args[0].s ? -1 : sb.s > args[0].s ? 1 : 0;
      case 'capacity': return Math.max(16, sb.s.length);
      default: throw err(`StringBuilder.${name}() is not supported`, line);
    }
  }

  // ------------------------------------------------------------ arrays / vectors / lists
  const elemT = (a) => a.et || null;
  const conv = (a, v) => { const t = elemT(a); return t ? I.coerce(v, t) : v; };
  const put = (a, v) => { const t = elemT(a); let x = t ? I.coerce(v, t) : v; if (I.lang === 'cpp') x = (x instanceof Obj && t && !t.ptr && !t.ref && !x.heap) ? V.cloneObj(x) : (x !== null && typeof x === 'object' && !(x instanceof Obj) && !(t && t.ptr) ? cloneVal(x) : x); return x; };
  const needNonEmpty = (a, what, line) => { if (!a.length) throw err(I.lang === 'java' ? 'NoSuchElementException' : `${what}() called on an empty container (undefined behaviour in C++)`, line, 'NoSuchElementException'); };
  const isBoxedArg = (node) => {
    if (!node) return false;
    if (node.k === 'cast') return /^(Integer|Object|Long|Character)$/.test(node.type.name);
    if (node.k === 'call' && node.callee.k === 'member' && node.callee.obj.k === 'id' && /^(Integer|Long|Character)$/.test(node.callee.obj.name) && node.callee.name === 'valueOf') return true;
    if (node.k === 'id') { const r = I.env.lookup(node.name); return !!(r && r.ty && /^(Integer|Long|Character|Object)$/.test(r.ty.name)); }
    return false;
  };

  function arrayMethod(a, name, args, ref, n) {
    const line = n.line;
    const java = I.lang === 'java';
    switch (name) {
      case 'size': case 'length': return a.length;
      case 'empty': case 'isEmpty': return a.length === 0;
      case 'push_back': case 'emplace_back': case 'add': case 'addLast': case 'offer': case 'offerLast': case 'append': {
        if (name === 'add' && args.length === 2) { const i = N(args[0]); if (i < 0 || i > a.length) throw err(`IndexOutOfBoundsException: Index: ${i}, Size: ${a.length}`, line, 'IndexOutOfBoundsException'); a.splice(i, 0, put(a, args[1])); return undefined; }
        if (name === 'emplace_back' && elemT(a) && args.length !== 1 && (elemT(a).name === 'pair' || elemT(a).name === 'tuple' || I.isUserClass(elemT(a).name))) a.push(I.constructTyped(elemT(a), args, false, line)); else if (name === 'emplace_back' && elemT(a) && I.isUserClass(elemT(a).name) && !(args[0] instanceof Obj)) a.push(I.constructTyped(elemT(a), args, false, line)); else a.push(put(a, args[0]));
        return java && name === 'add' ? true : undefined;
      }
      case 'push_front': case 'addFirst': case 'emplace_front': a.unshift(put(a, args[0])); return undefined;
      case 'pop_back': needNonEmpty(a, 'pop_back', line); a.pop(); return undefined;
      case 'pop_front': needNonEmpty(a, 'pop_front', line); a.shift(); return undefined;
      case 'removeFirst': case 'pollFirst': case 'poll': if (!a.length) { if (name === 'removeFirst') throw noSuch(line); return null; } return a.shift();
      case 'removeLast': case 'pollLast': if (!a.length) { if (name === 'removeLast') throw noSuch(line); return null; } return a.pop();
      case 'back': case 'getLast': case 'lastElement': needNonEmpty(a, 'back', line); return a[a.length - 1];
      case 'front': case 'getFirst': case 'firstElement': case 'peekFirst': needNonEmpty(a, 'front', line); return a[0];
      case 'peek': return a.length ? a[0] : null;
      case 'at': case 'get': { const i = N(args[0]); if (i < 0 || i >= a.length) throw err(java ? `IndexOutOfBoundsException: Index ${i} out of bounds for length ${a.length}` : `out_of_range: vector::at (index ${i} >= size ${a.length})`, line, java ? 'IndexOutOfBoundsException' : 'out_of_range'); return a[i]; }
      case 'set': { const i = N(args[0]); if (i < 0 || i >= a.length) throw err(`IndexOutOfBoundsException: Index ${i} out of bounds for length ${a.length}`, line, 'IndexOutOfBoundsException'); const o = a[i]; a[i] = put(a, args[1]); return o; }
      case 'begin': return new Iter(a, 0);
      case 'end': return new Iter(a, a.length);
      case 'rbegin': return new Iter(a, a.length - 1, null, true);
      case 'rend': return new Iter(a, -1, null, true);
      case 'clear': a.length = 0; return undefined;
      case 'data': return a;
      case 'capacity': return Math.max(a.length, 1);
      case 'reserve': case 'shrink_to_fit': case 'ensureCapacity': case 'trimToSize': return undefined;
      case 'resize': { const k = N(args[0]); if (k < a.length) a.length = k; else while (a.length < k) a.push(args.length > 1 ? put(a, args[1]) : I.defaultValue(a.et || { name: 'int', args: [], ptr: 0, dims: 0 })); return undefined; }
      case 'assign': { if (args[0] instanceof Iter) { const r = I.range(args[0], args[1]); a.length = 0; for (const x of r.items) a.push(cloneVal(x)); } else { const k = N(args[0]); a.length = 0; for (let i = 0; i < k; i++) a.push(put(a, args[1])); } return undefined; }
      case 'swap': { const o = args[0]; const t = a.slice(); a.length = 0; a.push(...o); o.length = 0; o.push(...t); return undefined; }
      case 'insert': {
        if (args[0] instanceof Iter) { // C++
          const p = args[0].pos;
          if (p < 0 || p > a.length) throw err('insert position is outside the vector', line);
          let items;
          if (args.length === 2) items = [put(a, args[1])];
          else if (args.length === 3 && args[1] instanceof Iter) items = I.range(args[1], args[2]).items.map(cloneVal);
          else items = new Array(N(args[1])).fill(0).map(() => put(a, args[2]));
          a.splice(p, 0, ...items);
          return new Iter(a, p);
        }
        break;
      }
      case 'emplace': { const p = args[0].pos; a.splice(p, 0, args.length > 2 && elemT(a) ? I.constructTyped(elemT(a), args.slice(1), false, line) : put(a, args[1])); return new Iter(a, p); }
      case 'erase': {
        if (!(args[0] instanceof Iter)) break;
        const p = args[0].pos;
        const q = args[1] instanceof Iter ? args[1].pos : p + 1;
        if (p < 0 || q > a.length || p > q || (!(args[1] instanceof Iter) && p >= a.length)) throw err('erase() iterator is out of range (erasing end() or an invalid position)', line);
        a.splice(p, q - p);
        return new Iter(a, p);
      }
      case 'addAll': { const src = args[args.length - 1]; const items = Array.isArray(src) ? src : src instanceof SetObj ? src.keys() : src instanceof Seq ? src.a : []; if (args.length === 2) a.splice(N(args[0]), 0, ...items); else a.push(...items); return true; }
      case 'remove': {
        if (!java) return undefined;
        const x = args[0];
        if (typeof x === 'number' && !isBoxedArg(n.args[0])) { const i = x; if (i < 0 || i >= a.length) throw err(`IndexOutOfBoundsException: Index ${i} out of bounds for length ${a.length}`, line, 'IndexOutOfBoundsException'); return a.splice(i, 1)[0]; }
        const i = a.findIndex((e) => I.eq(e, x)); if (i >= 0) { a.splice(i, 1); return true; } return false;
      }
      case 'removeIf': { const keep = a.filter((x) => !I.truthy(I.callValue(args[0], [x]))); const ch = keep.length !== a.length; a.length = 0; a.push(...keep); return ch; }
      case 'removeAll': { const other = args[0]; const items = Array.isArray(other) ? other : other.keys ? other.keys() : []; const keep = a.filter((x) => !items.some((y) => I.eq(x, y))); a.length = 0; a.push(...keep); return true; }
      case 'retainAll': { const other = args[0]; const items = Array.isArray(other) ? other : other.keys ? other.keys() : []; const keep = a.filter((x) => items.some((y) => I.eq(x, y))); a.length = 0; a.push(...keep); return true; }
      case 'contains': return a.some((x) => I.eq(x, args[0]));
      case 'containsAll': return args[0].every((y) => a.some((x) => I.eq(x, y)));
      case 'indexOf': return a.findIndex((x) => I.eq(x, args[0]));
      case 'lastIndexOf': { for (let i = a.length - 1; i >= 0; i--) if (I.eq(a[i], args[0])) return i; return -1; }
      case 'sort': { const cmp = args[0] ? I.makeCmp(args[0]) : (x, y) => I.cmpVals(x, y); a.sort(cmp); return undefined; }
      case 'reverse': a.reverse(); return undefined;
      case 'unique': { const out = []; for (const x of a) if (!out.length || !I.eq(out[out.length - 1], x)) out.push(x); a.length = 0; a.push(...out); return undefined; }
      case 'subList': { const f = N(args[0]), t = N(args[1]); if (f < 0 || t > a.length || f > t) throw err(`IndexOutOfBoundsException: fromIndex ${f}, toIndex ${t}, size ${a.length}`, line, 'IndexOutOfBoundsException'); const r = a.slice(f, t); r.et = a.et; return r; }
      case 'toArray': { const r = a.slice(); r.et = a.et; return r; }
      case 'iterator': case 'listIterator': return new Iter(a, 0);
      case 'forEach': for (const x of a.slice()) I.callValue(args[0], [x]); return undefined;
      case 'equals': return equals(a, args[0]);
      case 'hashCode': return V.javaHash(a);
      case 'toString': return I.str(a);
      case 'clone': return cloneVal(a);
      case 'fill': for (let i = 0; i < a.length; i++) a[i] = args[0]; return undefined;
      case 'stream': case 'parallelStream': throw new Unsupported('Java streams are not supported by the visualizer', line);
      case 'replaceAll': for (let i = 0; i < a.length; i++) a[i] = I.callValue(args[0], [a[i]]); return undefined;
      case 'push': a.push(args[0]); return args[0];
      case 'pop': return a.pop();
      default: break;
    }
    if (name === 'length') return a.length;
    throw err(`Unknown method "${name}" on a vector/list/array`, line);
  }

  // ------------------------------------------------------------ stack / queue / deque / priority queue
  function seqMethod(q, name, args, n) {
    const line = n.line;
    const a = q.a;
    const java = I.lang === 'java';
    const put2 = (v) => (q.et ? I.coerce(v, q.et) : v);
    const empty = (what) => { throw err(java ? 'NoSuchElementException' : `${what}() called on an empty ${q.kind} (undefined behaviour in C++)`, line, 'NoSuchElementException'); };
    const mk = (args2) => (q.et && (q.et.name === 'pair' || q.et.name === 'tuple' || I.isUserClass(q.et.name)) && !(args2.length === 1 && (args2[0] instanceof Pair || args2[0] instanceof Obj || args2[0] instanceof Tup)) ? I.constructTyped(q.et, args2, false, line) : args2[0]);
    switch (name) {
      case 'size': return a.length;
      case 'empty': case 'isEmpty': return a.length === 0;
      case 'clear': a.length = 0; return undefined;
      case 'contains': return a.some((x) => I.eq(x, args[0]));
      case 'iterator': return new Iter(q, 0, q.kind === 'pq' ? a.slice() : a);
      case 'toString': return I.str(q);
      case 'stream': throw new Unsupported('Java streams are not supported by the visualizer', line);
      case 'forEach': for (const x of a.slice()) I.callValue(args[0], [x]); return undefined;
      case 'toArray': return a.slice();
      default: break;
    }
    if (q.kind === 'pq') {
      switch (name) {
        case 'push': case 'add': case 'offer': I.pqPush(q, put2(args[0])); return java ? true : undefined;
        case 'emplace': I.pqPush(q, put2(mk(args))); return undefined;
        case 'pop': if (!a.length) { if (java) return null; empty('pop'); } return a.shift();
        case 'poll': return a.length ? a.shift() : null;
        case 'remove': if (!args.length) { if (!a.length) throw noSuch(line); return a.shift(); } { const i = a.findIndex((x) => I.eq(x, args[0])); if (i >= 0) { a.splice(i, 1); return true; } return false; }
        case 'top': if (!a.length) empty('top'); return a[0];
        case 'peek': return a.length ? a[0] : null;
        case 'element': if (!a.length) throw noSuch(line); return a[0];
        case 'addAll': for (const x of args[0].a || args[0]) I.pqPush(q, x); return true;
        default: break;
      }
    } else if (q.kind === 'stack') {
      switch (name) {
        case 'push': a.push(put2(args[0])); return java ? args[0] : undefined;
        case 'emplace': a.push(put2(mk(args))); return undefined;
        case 'pop': if (!a.length) { if (java) { const e = new RuntimeError('EmptyStackException', line); e.exc = 'EmptyStackException'; e.catchable = true; throw e; } empty('pop'); } return a.pop();
        case 'top': if (!a.length) empty('top'); return a[a.length - 1];
        case 'peek': if (!a.length) { const e = new RuntimeError('EmptyStackException', line); e.exc = 'EmptyStackException'; e.catchable = true; throw e; } return a[a.length - 1];
        case 'empty': return a.length === 0;
        case 'search': { for (let i = a.length - 1; i >= 0; i--) if (I.eq(a[i], args[0])) return a.length - i; return -1; }
        case 'get': case 'elementAt': { const i = N(args[0]); if (i < 0 || i >= a.length) throw err(`ArrayIndexOutOfBoundsException: ${i}`, line, 'ArrayIndexOutOfBoundsException'); return a[i]; }
        case 'firstElement': return a[0];
        case 'lastElement': return a[a.length - 1];
        case 'add': a.push(args[0]); return true;
        default: break;
      }
    } else if (q.kind === 'queue') { // C++ queue
      switch (name) {
        case 'push': case 'add': case 'offer': a.push(put2(args[0])); return java ? true : undefined;
        case 'emplace': a.push(put2(mk(args))); return undefined;
        case 'pop': if (!a.length) empty('pop'); a.shift(); return undefined;
        case 'poll': return a.length ? a.shift() : null;
        case 'front': case 'peek': case 'element': if (!a.length) { if (name === 'peek') return null; empty('front'); } return a[0];
        case 'back': if (!a.length) empty('back'); return a[a.length - 1];
        case 'remove': if (!a.length) throw noSuch(line); return a.shift();
        default: break;
      }
    } else { // Java ArrayDeque / LinkedList (front = index 0)
      switch (name) {
        case 'push': case 'addFirst': case 'offerFirst': a.unshift(put2(args[0])); return name === 'offerFirst' ? true : undefined;
        case 'add': case 'addLast': case 'offer': case 'offerLast': case 'append': if (name === 'add' && args.length === 2) { a.splice(N(args[0]), 0, args[1]); return undefined; } a.push(put2(args[0])); return true;
        case 'pop': case 'removeFirst': case 'element': case 'getFirst': if (!a.length) throw noSuch(line); return name === 'element' || name === 'getFirst' ? a[0] : a.shift();
        case 'remove': if (!args.length) { if (!a.length) throw noSuch(line); return a.shift(); } { const x = args[0]; if (typeof x === 'number' && !isBoxedArg(n.args[0]) && !(q.et && /Integer|int/.test(q.et.name) && q.kind === 'deque' && false)) { if (x < 0 || x >= a.length) throw err(`IndexOutOfBoundsException: Index: ${x}, Size: ${a.length}`, line, 'IndexOutOfBoundsException'); return a.splice(x, 1)[0]; } const i = a.findIndex((e) => I.eq(e, x)); if (i >= 0) { a.splice(i, 1); return true; } return false; }
        case 'poll': case 'pollFirst': return a.length ? a.shift() : null;
        case 'pollLast': return a.length ? a.pop() : null;
        case 'removeLast': if (!a.length) throw noSuch(line); return a.pop();
        case 'peek': case 'peekFirst': return a.length ? a[0] : null;
        case 'peekLast': return a.length ? a[a.length - 1] : null;
        case 'getLast': if (!a.length) throw noSuch(line); return a[a.length - 1];
        case 'get': { const i = N(args[0]); if (i < 0 || i >= a.length) throw err(`IndexOutOfBoundsException: Index: ${i}, Size: ${a.length}`, line, 'IndexOutOfBoundsException'); return a[i]; }
        case 'set': { const i = N(args[0]); const o = a[i]; a[i] = args[1]; return o; }
        case 'indexOf': return a.findIndex((x) => I.eq(x, args[0]));
        case 'descendingIterator': return new Iter(q, 0, a.slice().reverse());
        case 'addAll': for (const x of args[0].a || args[0]) a.push(x); return true;
        default: break;
      }
    }
    throw err(`Unknown method "${name}" on a ${q.kind}`, line);
  }

  // ------------------------------------------------------------ map
  function mapMethod(m, name, args, ref, n) {
    const line = n.line;
    const java = I.lang === 'java';
    const lookup = (k) => (m.multi ? (mapKeys(m, k).map((x) => m.m.get(x))[0] || null) : I.mapEntry(m, k, false));
    const es = () => m.entries();
    const entryAt = (idx) => es()[idx] || null;
    switch (name) {
      case 'size': return m.size;
      case 'empty': case 'isEmpty': return m.size === 0;
      case 'clear': m.m.clear(); m.dirty(); return undefined;
      case 'count': return m.multi ? mapKeys(m, args[0]).length : (lookup(args[0]) ? 1 : 0);
      case 'containsKey': case 'contains': return !!lookup(args[0]);
      case 'containsValue': return es().some((e) => I.eq(e.second, args[0]));
      case 'find': { const e = lookup(args[0]); if (!e) return mkIter(m, es().length); return mkIter(m, es().indexOf(e)); }
      case 'begin': return mkIter(m, 0);
      case 'end': return mkIter(m, es().length);
      case 'rbegin': return new Iter(m, es().length - 1, es(), true);
      case 'rend': return new Iter(m, -1, es(), true);
      case 'at': { const e = lookup(args[0]); if (!e) throw err(`out_of_range: map::at — key ${I.str(args[0])} is not in the map`, line, 'out_of_range'); return e.second; }
      case 'get': { const e = lookup(args[0]); return e ? e.second : null; }
      case 'getOrDefault': { const e = lookup(args[0]); return e ? e.second : args[1]; }
      case 'put': { const old = I.mapPut(m, args[0], args[1]); return old; }
      case 'insert': {
        let k, v;
        if (args[0] instanceof Pair) { k = args[0].first; v = args[0].second; } else if (args[0] instanceof Iter) { for (const e of I.range(args[0], args[1]).items) I.mapPut(m, e.first, e.second); return undefined; } else { k = args[0]; v = args[1]; }
        const had = !m.multi && lookup(k);
        if (!had) I.mapPut(m, k, v);
        return new Pair(mkIter(m, es().indexOf(lookup(k))), !had);
      }
      case 'emplace': case 'try_emplace': { const k = args[0]; const v = args.length > 2 && m.vt ? I.constructTyped(m.vt, args.slice(1), false, line) : args[1] instanceof Pair && name === 'emplace' ? args[1] : args[1]; const had = !m.multi && lookup(k); if (!had) I.mapPut(m, k, v === undefined ? (m.vt ? I.defaultValue(m.vt) : null) : v); return new Pair(mkIter(m, es().indexOf(lookup(k))), !had); }
      case 'insert_or_assign': I.mapPut(m, args[0], args[1]); return undefined;
      case 'putIfAbsent': { const e = lookup(args[0]); if (e && e.second !== null) return e.second; I.mapPut(m, args[0], args[1]); return null; }
      case 'remove': { if (!args.length) return undefined; const e = lookup(args[0]); delKey(m, args[0]); return e ? e.second : null; }
      case 'erase': {
        if (args[0] instanceof Iter) { const it = args[0]; const pos = it.pos; const e = it.keys[pos]; if (!e) throw err('erase() iterator is out of range', line); for (const [k, x] of m.m) if (x === e) { m.m.delete(k); break; } m.dirty(); return mkIter(m, pos); }
        return delKey(m, args[0]);
      }
      case 'lower_bound': case 'ceilingKey': case 'ceilingEntry': case 'upper_bound': case 'higherKey': case 'higherEntry': case 'floorKey': case 'floorEntry': case 'lowerKey': case 'lowerEntry': {
        const list = es();
        const c = cmpOf(m);
        const lo = (strict) => { let a = 0, b = list.length; while (a < b) { const mid = (a + b) >> 1; const r = c(list[mid].first, args[0]); if (strict ? r <= 0 : r < 0) a = mid + 1; else b = mid; } return a; };
        if (name === 'lower_bound') return mkIter(m, lo(false));
        if (name === 'upper_bound') return mkIter(m, lo(true));
        let idx;
        if (name.startsWith('ceiling')) idx = lo(false);
        else if (name.startsWith('higher')) idx = lo(true);
        else if (name.startsWith('floor')) idx = lo(true) - 1;
        else idx = lo(false) - 1;
        const e = list[idx];
        if (!e || idx < 0) return null;
        return name.endsWith('Key') ? e.first : e;
      }
      case 'firstKey': case 'lastKey': { const list = es(); if (!list.length) throw noSuch(line); return name === 'firstKey' ? list[0].first : list[list.length - 1].first; }
      case 'firstEntry': case 'lastEntry': { const list = es(); if (!list.length) return null; return name === 'firstEntry' ? list[0] : list[list.length - 1]; }
      case 'pollFirstEntry': case 'pollLastEntry': { const list = es(); if (!list.length) return null; const e = name === 'pollFirstEntry' ? list[0] : list[list.length - 1]; delKey(m, e.first); return e; }
      case 'keySet': case 'navigableKeySet': { const s = new SetObj('set', true, m.cmp); s.kt = m.kt; for (const e of es()) I.setAdd(s, e.first); s.jhash = false; s.ordered = m.ordered; if (!m.ordered) { s.ordered = false; s.order = es().map((e) => e.first); } return m.ordered ? s : es().map((e) => e.first); }
      case 'values': return es().map((e) => e.second);
      case 'entrySet': return es().slice();
      case 'putAll': for (const e of args[0].entries()) I.mapPut(m, e.first, e.second); return undefined;
      case 'computeIfAbsent': { const e = lookup(args[0]); if (e && e.second !== null) return e.second; const v = I.callValue(args[1], [args[0]]); if (v !== null) I.mapPut(m, args[0], v); return v; }
      case 'computeIfPresent': { const e = lookup(args[0]); if (!e || e.second === null) return null; const v = I.callValue(args[1], [args[0], e.second]); if (v === null) delKey(m, args[0]); else e.second = v; return v; }
      case 'compute': { const e = lookup(args[0]); const v = I.callValue(args[1], [args[0], e ? e.second : null]); if (v === null) delKey(m, args[0]); else I.mapPut(m, args[0], v); return v; }
      case 'merge': { const e = lookup(args[0]); const v = e && e.second !== null ? I.callValue(args[2], [e.second, args[1]]) : args[1]; if (v === null) delKey(m, args[0]); else I.mapPut(m, args[0], v); return v; }
      case 'forEach': for (const e of es().slice()) I.callValue(args[0], [e.first, e.second]); return undefined;
      case 'headMap': case 'tailMap': case 'subMap': case 'descendingMap': { const out = new MapObj('map', true, m.cmp); out.kt = m.kt; out.vt = m.vt; const c = cmpOf(m); for (const e of es()) { const k = e.first; let ok = true; if (name === 'headMap') ok = c(k, args[0]) < 0 || (args[1] === true && c(k, args[0]) === 0); else if (name === 'tailMap') ok = c(k, args[0]) > 0 || (args[1] !== false && c(k, args[0]) === 0); else if (name === 'subMap') ok = c(k, args[0]) >= 0 && c(k, args[args.length === 4 ? 2 : 1]) < 0; if (ok) I.mapPut(out, k, e.second); } if (name === 'descendingMap') { out.cmp = (a, b) => c(b, a); } return out; }
      case 'swap': { const o = args[0]; const t = new Map(m.m); m.m = new Map(o.m); o.m = t; m.dirty(); o.dirty(); return undefined; }
      case 'equals': return equals(es().map((e) => [e.first, e.second]), args[0].entries().map((e) => [e.first, e.second]));
      case 'toString': return I.str(m);
      case 'hashCode': return 0;
      default: break;
    }
    void java; void entryAt;
    throw err(`Unknown map method "${name}"`, line);
  }

  // ------------------------------------------------------------ set
  function setMethod(s, name, args, n) {
    const line = n.line;
    const list = () => s.keys();
    const c = cmpOf(s);
    const bsearch = (strict) => { const l = list(); let a = 0, b = l.length; while (a < b) { const mid = (a + b) >> 1; const r = c(l[mid], args[0]); if (strict ? r <= 0 : r < 0) a = mid + 1; else b = mid; } return a; };
    const has = (k) => mapKeys(s, k).length > 0;
    switch (name) {
      case 'size': return s.size;
      case 'empty': case 'isEmpty': return s.size === 0;
      case 'clear': s.m.clear(); s.dirty(); return undefined;
      case 'insert': case 'add': case 'emplace': {
        if (args[0] instanceof Iter) { for (const x of I.range(args[0], args[1]).items) I.setAdd(s, x); return undefined; }
        const had = !s.multi && has(args[0]);
        if (!had) I.setAdd(s, args[0]);
        if (I.lang === 'java') return !had;
        const idx = list().findIndex((x) => I.eq(x, args[0]));
        return new Pair(new Iter(s, idx, list()), !had);
      }
      case 'count': return mapKeys(s, args[0]).length;
      case 'contains': return has(args[0]);
      case 'find': { const l = list(); const idx = l.findIndex((x) => I.eq(x, I.coerce(args[0], s.kt))); return new Iter(s, idx < 0 ? l.length : idx, l); }
      case 'begin': return new Iter(s, 0, list());
      case 'end': return new Iter(s, list().length, list());
      case 'rbegin': return new Iter(s, list().length - 1, list(), true);
      case 'rend': return new Iter(s, -1, list(), true);
      case 'erase': {
        if (args[0] instanceof Iter) { const it = args[0]; const e = it.keys[it.pos]; if (e === undefined) throw err('erase() iterator is out of range', line); for (const [k, x] of s.m) if (x === e) { s.m.delete(k); break; } s.dirty(); return new Iter(s, it.pos, list()); }
        return delKey(s, args[0]);
      }
      case 'remove': return delKey(s, args[0]) > 0;
      case 'lower_bound': return new Iter(s, bsearch(false), list());
      case 'upper_bound': return new Iter(s, bsearch(true), list());
      case 'first': { const l = list(); if (!l.length) throw noSuch(line); return l[0]; }
      case 'last': { const l = list(); if (!l.length) throw noSuch(line); return l[l.length - 1]; }
      case 'pollFirst': { const l = list(); if (!l.length) return null; delKey(s, l[0]); return l[0]; }
      case 'pollLast': { const l = list(); if (!l.length) return null; delKey(s, l[l.length - 1]); return l[l.length - 1]; }
      case 'ceiling': { const i = bsearch(false); const l = list(); return i < l.length ? l[i] : null; }
      case 'higher': { const i = bsearch(true); const l = list(); return i < l.length ? l[i] : null; }
      case 'floor': { const i = bsearch(true) - 1; return i >= 0 ? list()[i] : null; }
      case 'lower': { const i = bsearch(false) - 1; return i >= 0 ? list()[i] : null; }
      case 'iterator': return new Iter(s, 0, list());
      case 'descendingIterator': return new Iter(s, 0, list().slice().reverse());
      case 'descendingSet': return list().slice().reverse();
      case 'addAll': { let ch = false; const src = args[0]; for (const x of (Array.isArray(src) ? src : src.keys ? src.keys() : src.a)) ch = I.setAdd(s, x) || ch; return ch; }
      case 'removeAll': { let ch = false; const src = args[0]; for (const x of (Array.isArray(src) ? src : src.keys())) ch = delKey(s, x) > 0 || ch; return ch; }
      case 'retainAll': { const src = args[0]; const keep = Array.isArray(src) ? src : src.keys(); let ch = false; for (const x of list()) if (!keep.some((y) => I.eq(x, y))) { delKey(s, x); ch = true; } return ch; }
      case 'containsAll': return (Array.isArray(args[0]) ? args[0] : args[0].keys()).every((x) => has(x));
      case 'headSet': case 'tailSet': case 'subSet': { const out = new SetObj('set', true, s.cmp); out.kt = s.kt; for (const k of list()) { const r1 = c(k, args[0]); let ok; if (name === 'headSet') ok = r1 < 0 || (args[1] === true && r1 === 0); else if (name === 'tailSet') ok = r1 > 0 || (args[1] !== false && r1 === 0); else ok = r1 >= 0 && c(k, args[args.length === 4 ? 2 : 1]) < 0; if (ok) I.setAdd(out, k); } return out; }
      case 'forEach': for (const x of list().slice()) I.callValue(args[0], [x]); return undefined;
      case 'removeIf': { let ch = false; for (const x of list()) if (I.truthy(I.callValue(args[0], [x]))) { delKey(s, x); ch = true; } return ch; }
      case 'toArray': return list().slice();
      case 'stream': throw new Unsupported('Java streams are not supported by the visualizer', line);
      case 'equals': return equals(list(), args[0].keys());
      case 'toString': return I.str(s);
      case 'hashCode': return 0;
      case 'swap': { const o = args[0]; const t = new Map(s.m); s.m = new Map(o.m); o.m = t; s.dirty(); o.dirty(); return undefined; }
      default: break;
    }
    throw err(`Unknown set method "${name}"`, line);
  }
  void UNINIT; void Lambda; void Tup;
}
