// Standard-library surface of the C++ / Java interpreter: constants, formatting, free functions and static classes.
// Container / string methods live in methods.js.
import * as V from './values.js';
import { installMethods } from './methods.js';

const {
  Dbl, Chr, Pair, Tup, Obj, UNINIT, Cell, ElemRef, FieldRef, FnRef, MapObj, SetObj, Seq, Iter, Lambda, StrBuilder,
  RuntimeError, Unsupported, ThrowSignal, cloneVal, equals,
} = V;

const I32_MAX = 2147483647, I32_MIN = -2147483648;
const L_MAX = 9223372036854775807n, L_MIN = -9223372036854775808n;

const STATIC_CLASSES = new Set(['Math', 'Integer', 'Long', 'Double', 'Character', 'Boolean', 'String', 'Arrays', 'Collections', 'List', 'Set', 'Map', 'Objects', 'System', 'Comparator', 'Float', 'Short', 'Byte', 'StringBuilder', 'Collectors', 'Stream', 'IntStream', 'Optional', 'ThreadLocalRandom', 'Entry', 'Thread', 'LocalDate', 'BigInteger', 'BigDecimal']);

export function fmtG(x, p = 6) {
  if (!Number.isFinite(x)) return Number.isNaN(x) ? 'nan' : x < 0 ? '-inf' : 'inf';
  if (x === 0) return Object.is(x, -0) ? '-0' : '0';
  if (p === 0) p = 1;
  const exp = Math.floor(Math.log10(Math.abs(Number(x.toPrecision(p)))));
  if (exp < -5 || exp >= p) {
    let [m, e] = x.toExponential(p - 1).split('e');
    if (m.includes('.')) m = m.replace(/0+$/, '').replace(/\.$/, '');
    const sign = e[0] === '-' ? '-' : '+';
    const digits = e.replace(/^[-+]/, '').padStart(2, '0');
    return `${m}e${sign}${digits}`;
  }
  let s = x.toPrecision(p);
  if (s.includes('e')) s = String(Number(s));
  if (s.includes('.')) s = s.replace(/0+$/, '').replace(/\.$/, '');
  return s;
}

export function javaDouble(x) {
  if (Number.isNaN(x)) return 'NaN';
  if (!Number.isFinite(x)) return x < 0 ? '-Infinity' : 'Infinity';
  if (x === 0) return Object.is(x, -0) ? '-0.0' : '0.0';
  const a = Math.abs(x);
  if (a >= 1e-3 && a < 1e7) { const s = String(x); return s.includes('.') ? s : `${s}.0`; }
  let [m, e] = x.toExponential().split('e');
  if (!m.includes('.')) m += '.0';
  return `${m}E${e.replace('+', '')}`;
}

export function installLib(I) {
  const lang = () => I.lang;
  const COUT = { isStream: true, name: 'cout' };
  const CERR = { isStream: true, name: 'cerr', err: true };
  const ENDL = { manip: 'endl' };
  const JOUT = { isStream: true, name: 'System.out', java: true };
  const JERR = { isStream: true, name: 'System.err', java: true, err: true };
  I.COUT = COUT;

  installMethods(I);

  // ------------------------------------------------------------ constants
  I.constantValue = function constantValue(name) {
    switch (name) {
      case 'INT_MAX': return I32_MAX;
      case 'INT_MIN': return I32_MIN;
      case 'UINT_MAX': return 4294967295;
      case 'LLONG_MAX': case 'LONG_MAX': case 'INT64_MAX': return L_MAX;
      case 'LLONG_MIN': case 'LONG_MIN': case 'INT64_MIN': return L_MIN;
      case 'ULLONG_MAX': case 'UINT64_MAX': return 18446744073709551615n;
      case 'INT32_MAX': return I32_MAX;
      case 'INT32_MIN': return I32_MIN;
      case 'SHRT_MAX': return 32767;
      case 'SHRT_MIN': return -32768;
      case 'CHAR_BIT': return 8;
      case 'CHAR_MAX': return Chr.of(127);
      case 'CHAR_MIN': return Chr.of(-128 & 0xFF);
      case 'DBL_MAX': return new Dbl(Number.MAX_VALUE);
      case 'DBL_MIN': return new Dbl(2.2250738585072014e-308);
      case 'DBL_EPSILON': return new Dbl(Number.EPSILON);
      case 'INFINITY': case 'HUGE_VAL': return new Dbl(Infinity);
      case 'NAN': return new Dbl(NaN);
      case 'M_PI': return new Dbl(Math.PI);
      case 'M_E': return new Dbl(Math.E);
      case 'npos': return -1;
      case 'RAND_MAX': return 2147483647;
      case 'cout': return COUT;
      case 'cerr': case 'clog': return CERR;
      case 'endl': return ENDL;
      case 'fixed': return { manip: 'fixed' };
      case 'boolalpha': return { manip: 'boolalpha' };
      case 'cin': return { isStream: true, name: 'cin', input: true };
      case 'System': return { $static: 'System' };
      case 'true_type': return true;
      default: return undefined;
    }
  };

  const NUMLIM = { int: [I32_MIN, I32_MAX], uint: [0, 4294967295], long: [L_MIN, L_MAX], ulong: [0n, 18446744073709551615n], short: [-32768, 32767], char: [Chr.of(0x80), Chr.of(127)], uchar: [Chr.of(0), Chr.of(255)] };

  I.builtinStatic = function builtinStatic(cname, name, line, typeNode) {
    switch (cname) {
      case 'Integer': if (name === 'MAX_VALUE') return I32_MAX; if (name === 'MIN_VALUE') return I32_MIN; if (name === 'SIZE') return 32; break;
      case 'Long': if (name === 'MAX_VALUE') return L_MAX; if (name === 'MIN_VALUE') return L_MIN; break;
      case 'Short': if (name === 'MAX_VALUE') return 32767; if (name === 'MIN_VALUE') return -32768; break;
      case 'Byte': if (name === 'MAX_VALUE') return 127; if (name === 'MIN_VALUE') return -128; break;
      case 'Character': if (name === 'MAX_VALUE') return Chr.of(0xFFFF); if (name === 'MIN_VALUE') return Chr.of(0); break;
      case 'Double': case 'Float':
        switch (name) { case 'MAX_VALUE': return new Dbl(Number.MAX_VALUE); case 'MIN_VALUE': return new Dbl(5e-324); case 'POSITIVE_INFINITY': return new Dbl(Infinity); case 'NEGATIVE_INFINITY': return new Dbl(-Infinity); case 'NaN': return new Dbl(NaN); default: break; }
        break;
      case 'Math': if (name === 'PI') return new Dbl(Math.PI); if (name === 'E') return new Dbl(Math.E); break;
      case 'System': if (name === 'out') return JOUT; if (name === 'err') return JERR; if (name === 'in') return { isStream: true, input: true }; break;
      case 'Boolean': if (name === 'TRUE') return true; if (name === 'FALSE') return false; break;
      case 'string': if (name === 'npos') return -1; break;
      case 'std': return I.constantValue(name);
      default: break;
    }
    if (typeNode && (cname === 'numeric_limits')) return undefined;
    return undefined;
  };

  I.isBuiltinStaticClass = (n) => STATIC_CLASSES.has(n) || n === 'numeric_limits';

  // ------------------------------------------------------------ text conversion / output
  I.str = function str(v) {
    switch (typeof v) {
      case 'string': return v;
      case 'number': return String(v);
      case 'bigint': return v.toString();
      case 'boolean': return v ? 'true' : 'false';
      default: break;
    }
    if (v === null || v === undefined) return 'null';
    if (v instanceof Chr) return v.s;
    if (v instanceof Dbl) return javaDouble(v.v);
    if (v === UNINIT) return '0';
    if (v instanceof StrBuilder) return v.s;
    if (Array.isArray(v)) return `[${v.map((x) => I.str(x)).join(', ')}]`;
    if (v instanceof Pair) return `${I.str(v.first)}=${I.str(v.second)}`;
    if (v instanceof Tup) return `(${v.items.map((x) => I.str(x)).join(', ')})`;
    if (v instanceof MapObj) return `{${v.entries().map((e) => `${I.str(e.first)}=${I.str(e.second)}`).join(', ')}}`;
    if (v instanceof SetObj) return `[${v.keys().map((x) => I.str(x)).join(', ')}]`;
    if (v instanceof Seq) return `[${v.a.map((x) => I.str(x)).join(', ')}]`;
    if (v instanceof Obj) {
      if (v.cls.builtinException) return `${v.cls.name}: ${v.f.message}`;
      const m = I.findMethod(v.cls, 'toString', 0);
      if (m) return String(I.invoke(m, [], v, I.line));
      if (v.enumName !== undefined) return v.enumName;
      return `${v.cls.name}@${(0x1b6d3586 + v.id * 4099).toString(16)}`;
    }
    return String(v);
  };

  const cppFmt = (v) => {
    if (typeof v === 'string') return v;
    if (typeof v === 'boolean') return I.boolalpha ? (v ? 'true' : 'false') : (v ? '1' : '0');
    if (typeof v === 'number' || typeof v === 'bigint') return String(v);
    if (v instanceof Chr) return v.s;
    if (v instanceof Dbl) return I.fixed ? v.v.toFixed(I.prec) : fmtG(v.v, I.prec);
    if (v === null) return '0';
    if (v === UNINIT) return '0';
    if (v instanceof Obj) { const m = I.findMethod(v.cls, 'operator<<', 1); if (m) return I.str(v); return `${v.cls.name}@object`; }
    return I.str(v);
  };

  I.out = function out(s, stream) {
    if (stream && stream.err) return;
    I.stdout += s; I.pendingOut += s;
    if (I.stdout.length > 20000) { I.stdout = I.stdout.slice(-20000); }
  };

  I.streamOut = function streamOut(stream, v, node) {
    void node;
    if (stream.java) return stream;
    if (v && v.manip) {
      switch (v.manip) {
        case 'endl': I.out('\n', stream); break;
        case 'fixed': I.fixed = true; break;
        case 'boolalpha': I.boolalpha = true; break;
        case 'setprecision': I.prec = v.n; break;
        case 'setw': I.width = v.n; break;
        case 'setfill': I.fill = v.c; break;
        default: break;
      }
      return stream;
    }
    let s = cppFmt(v);
    if (I.width) { s = s.padStart(I.width, I.fill || ' '); I.width = 0; }
    I.out(s, stream);
    return stream;
  };

  /** printf / String.format */
  I.sprintf = function sprintf(fmt, args, java = false) {
    let ai = 0;
    return fmt.replace(/%([-+ 0,#]*)(\d+)?(?:\.(\d+))?(hh|h|ll|l|z|j|t|L)?([a-zA-Z%])/g, (m, flags, width, prec, len, conv) => {
      if (conv === '%') return '%';
      if (conv === 'n') return '\n';
      let a = args[ai++];
      let s;
      const num = (x) => (x instanceof Chr ? x.c : x instanceof Dbl ? x.v : typeof x === 'bigint' ? Number(x) : typeof x === 'boolean' ? (x ? 1 : 0) : x);
      switch (conv) {
        case 'd': case 'i': case 'u': {
          if (a instanceof Dbl && java) throw new RuntimeError('IllegalFormatConversionException: d != java.lang.Double', I.line);
          let n = typeof a === 'bigint' ? a : BigInt(Math.trunc(num(a) || 0));
          if (conv === 'u' && n < 0n) n = BigInt.asUintN(len === 'll' || len === 'l' ? 64 : 32, n);
          s = n.toString();
          if (flags.includes(',')) s = s.replace(/\B(?=(\d{3})+(?!\d))/g, ',');
          if (flags.includes('+') && n >= 0n) s = `+${s}`;
          break;
        }
        case 'f': case 'F': { const p = prec === undefined ? 6 : Number(prec); s = num(a).toFixed(p); if (flags.includes(',')) { const [i0, f0] = s.split('.'); s = i0.replace(/\B(?=(\d{3})+(?!\d))/g, ',') + (f0 ? `.${f0}` : ''); } if (flags.includes('+') && num(a) >= 0) s = `+${s}`; break; }
        case 'e': case 'E': { const p = prec === undefined ? 6 : Number(prec); s = num(a).toExponential(p).replace(/e([-+])(\d)$/, 'e$10$2'); if (conv === 'E') s = s.toUpperCase(); break; }
        case 'g': case 'G': s = fmtG(num(a), prec === undefined ? 6 : Number(prec)); break;
        case 'c': s = a instanceof Chr ? a.s : String.fromCharCode(num(a)); break;
        case 's': s = java ? I.str(a) : (typeof a === 'string' ? a : a instanceof Chr ? a.s : I.str(a)); if (prec !== undefined) s = s.slice(0, Number(prec)); break;
        case 'S': s = I.str(a).toUpperCase(); break;
        case 'b': case 'B': s = String(a !== null && a !== false); break;
        case 'x': s = (typeof a === 'bigint' ? BigInt.asUintN(64, a) : BigInt(num(a) >>> 0)).toString(16); break;
        case 'X': s = (typeof a === 'bigint' ? BigInt.asUintN(64, a) : BigInt(num(a) >>> 0)).toString(16).toUpperCase(); break;
        case 'o': s = (num(a) >>> 0).toString(8); break;
        case 'p': s = '0x7ffc0000'; break;
        default: return m;
      }
      if (width) {
        const w = Number(width);
        if (flags.includes('-')) s = s.padEnd(w, ' ');
        else if (flags.includes('0') && !['s', 'c'].includes(conv)) { const neg = /^[-+]/.test(s) ? s[0] : ''; s = neg + s.slice(neg.length).padStart(w - neg.length, '0'); } else s = s.padStart(w, ' ');
      }
      return s;
    });
  };

  // ------------------------------------------------------------ std functors
  I.stdFunctor = function stdFunctor(n) {
    const cmp = (f) => new FnRef((a) => f(a[0], a[1]), n);
    switch (n) {
      case 'greater': return cmp((a, b) => I.cmpVals(a, b) > 0);
      case 'less': return cmp((a, b) => I.cmpVals(a, b) < 0);
      case 'greater_equal': return cmp((a, b) => I.cmpVals(a, b) >= 0);
      case 'less_equal': return cmp((a, b) => I.cmpVals(a, b) <= 0);
      case 'equal_to': return cmp((a, b) => I.eq(a, b));
      case 'plus': return cmp((a, b) => I.binop('+', a, b));
      case 'minus': return cmp((a, b) => I.binop('-', a, b));
      case 'multiplies': return cmp((a, b) => I.binop('*', a, b));
      default: return null;
    }
  };

  // ------------------------------------------------------------ number helpers
  const N = (x) => I.num(x);
  const isFloatArg = (x) => x instanceof Dbl;
  const same = (a, b, r) => (a instanceof Dbl || b instanceof Dbl ? new Dbl(r) : r);
  const dbl = (x) => new Dbl(x);

  const maxmin = (isMax) => (args) => {
    let list = args;
    if (args.length === 1 && Array.isArray(args[0])) list = args[0];
    let best = list[0];
    for (let i = 1; i < list.length; i++) { const x = list[i]; const c = I.cmpVals(x, best); if (isMax ? c > 0 : c < 0) best = x; }
    if (list.some((x) => x instanceof Dbl) && !(best instanceof Dbl)) return dbl(N(best));
    if (list.some((x) => typeof x === 'bigint') && typeof best === 'number') return BigInt(best);
    return best;
  };

  const absf = (a) => {
    if (typeof a === 'number') return a === I32_MIN ? I32_MIN : Math.abs(a);
    if (typeof a === 'bigint') return a < 0n ? BigInt.asIntN(64, -a) : a;
    if (a instanceof Dbl) return dbl(Math.abs(a.v));
    if (a instanceof Chr) return Math.abs(a.c);
    return Math.abs(N(a));
  };

  const gcd = (a, b) => { if (typeof a === 'bigint' || typeof b === 'bigint') { let x = BigInt(a), y = BigInt(b); if (x < 0n) x = -x; if (y < 0n) y = -y; while (y) [x, y] = [y, x % y]; return x; } let x = Math.abs(a), y = Math.abs(b); while (y) [x, y] = [y, x % y]; return x; };

  const toStringNum = (v) => (v instanceof Dbl ? v.v.toFixed(6) : v instanceof Chr ? String(v.c) : String(v));

  const parseIntStr = (s, radix = 10, line) => {
    const t = typeof s === 'string' ? s : I.str(s);
    const re = radix === 10 ? /^\s*[-+]?\d+/ : null;
    if (I.lang === 'java') {
      const ok = radix === 10 ? /^[-+]?\d+$/.test(t) : new RegExp(`^[-+]?[0-9a-z]+$`, 'i').test(t) && !Number.isNaN(parseInt(t, radix));
      if (!ok) { const e = new RuntimeError(`NumberFormatException: For input string: "${t}"`, line); e.exc = 'NumberFormatException'; throw e; }
      return BigInt(radix === 10 ? t.replace(/^\+/, '') : parseInt(t, radix));
    }
    const m = re ? re.exec(t) : null;
    if (!m) { const e = new RuntimeError(`invalid_argument: stoi("${t}")`, line); e.exc = 'invalid_argument'; e.catchable = true; throw e; }
    return BigInt(m[0].trim().replace(/^\+/, ''));
  };

  // ------------------------------------------------------------ ranges (iterator pairs)
  const toIter = (x) => (x instanceof Iter ? x : Array.isArray(x) ? new Iter(x, 0) : x instanceof Seq ? new Iter(x.a, 0) : x);
  I.toIter = toIter;

  const isRefObj = (c) => c instanceof Cell || c instanceof ElemRef || c instanceof FieldRef || (c && c.constructor && c.constructor.name === 'StrIdxRef');

  /** view over [first, last): items (copy, in iteration order) and write(items2) to store back */
  I.range = function range(first, last, line = I.line) {
    first = toIter(first); last = toIter(last);
    if (!(first instanceof Iter) || !(last instanceof Iter)) throw new RuntimeError('Expected a pair of iterators (begin, end)', line);
    const c = first.coll;
    if (first.rev) {
      const arr = Array.isArray(c) ? c : null;
      const items = []; const idx = [];
      if (arr) for (let p = first.pos; p > last.pos; p--) { items.push(arr[p]); idx.push(p); }
      return { items, write: (it2) => { if (arr) it2.forEach((v, i) => { arr[idx[i]] = v; }); } };
    }
    if (Array.isArray(c)) {
      const lo = first.pos, hi = last.pos;
      if (lo < 0 || hi > c.length || lo > hi) throw new RuntimeError('Iterator range is invalid (begin must come before end and both must be inside the container)', line);
      return { items: c.slice(lo, hi), lo, hi, arr: c, write: (it2) => { for (let i = 0; i < it2.length; i++) c[lo + i] = it2[i]; } };
    }
    if (isRefObj(c)) { // string variable
      const s = c.get();
      const items = [...s.slice(first.pos, last.pos)].map((ch) => Chr.of(ch.charCodeAt(0)));
      return { items, write: (it2) => { c.set(s.slice(0, first.pos) + it2.map((x) => (x instanceof Chr ? x.s : String.fromCharCode(N(x)))).join('') + s.slice(last.pos)); } };
    }
    if (first.keys) return { items: first.keys.slice(first.pos, last.pos).map((e) => e), write: () => { throw new RuntimeError('Cannot modify elements of a set/map through iterators', line); } };
    throw new RuntimeError('Unsupported iterator range', line);
  };

  I.iterToArray = (a, b) => I.range(a, b).items;
  I.sliceIter = (arr, args) => { const r = I.range(args[0], args[1]); const out = r.items.map(cloneVal); const c = toIter(args[0]).coll; if (Array.isArray(c) && c.et) out.et = c.et; return out; };
  I.rangeStr = (a, b) => I.range(a, b).items.map((x) => (x instanceof Chr ? x.s : String.fromCharCode(N(x)))).join('');

  const sortItems = (items, cmp) => items.sort(cmp ? (a, b) => cmp(a, b) : (a, b) => I.cmpVals(a, b));
  const lessCmp = (f) => (f ? I.makeCmp(f) : null);

  // binary search helpers on a sorted item array: first index where !(item < x) / (x < item)
  const lowerIdx = (items, x, cmp) => { let lo = 0, hi = items.length; const c = cmp || ((a, b) => I.cmpVals(a, b)); while (lo < hi) { const m = (lo + hi) >> 1; if (c(items[m], x) < 0) lo = m + 1; else hi = m; } return lo; };
  const upperIdx = (items, x, cmp) => { let lo = 0, hi = items.length; const c = cmp || ((a, b) => I.cmpVals(a, b)); while (lo < hi) { const m = (lo + hi) >> 1; if (c(x, items[m]) < 0) hi = m; else lo = m + 1; } return lo; };
  I.lowerIdx = lowerIdx; I.upperIdx = upperIdx;

  // ------------------------------------------------------------ free functions (C++)
  const LV_ARGS = { swap: [0, 1], iter_swap: [0, 1], tie: [-1], getline: [1], reverse_ref: [] };

  I.builtinFreeExists = (name) => name in FREE || name in FREE_LV;

  const FREE_LV = {
    swap(refs) { const a = refs[0], b = refs[1]; const x = a.get(), y = b.get(); a.set(y); b.set(x); },
    iter_swap(args) { const a = args[0], b = args[1]; const ra = I.iterRef(a, I.line), rb = I.iterRef(b, I.line); const x = ra.get(); ra.set(rb.get()); rb.set(x); },
    tie(refs) { return { isTie: true, get: () => new Tup(refs.map((r) => r.get())), set: (t) => { const items = t instanceof Pair ? [t.first, t.second] : t instanceof Tup ? t.items : t; refs.forEach((r, i) => { if (r) r.set(items[i]); }); } }; },
  };

  const FREE = {
    // ---- numeric
    max: maxmin(true),
    min: maxmin(false),
    abs: (a) => absf(a[0]), labs: (a) => absf(a[0]), llabs: (a) => absf(a[0]), fabs: (a) => dbl(Math.abs(N(a[0]))),
    pow: (a) => dbl(Math.pow(N(a[0]), N(a[1]))),
    sqrt: (a) => dbl(Math.sqrt(N(a[0]))), cbrt: (a) => dbl(Math.cbrt(N(a[0]))),
    floor: (a) => dbl(Math.floor(N(a[0]))), ceil: (a) => dbl(Math.ceil(N(a[0]))), round: (a) => dbl(Math.sign(N(a[0])) * Math.round(Math.abs(N(a[0])))), trunc: (a) => dbl(Math.trunc(N(a[0]))),
    log: (a) => dbl(Math.log(N(a[0]))), log2: (a) => dbl(Math.log2(N(a[0]))), log10: (a) => dbl(Math.log10(N(a[0]))), exp: (a) => dbl(Math.exp(N(a[0]))),
    sin: (a) => dbl(Math.sin(N(a[0]))), cos: (a) => dbl(Math.cos(N(a[0]))), tan: (a) => dbl(Math.tan(N(a[0]))), atan: (a) => dbl(Math.atan(N(a[0]))), atan2: (a) => dbl(Math.atan2(N(a[0]), N(a[1]))), asin: (a) => dbl(Math.asin(N(a[0]))), acos: (a) => dbl(Math.acos(N(a[0]))),
    fmod: (a) => dbl(N(a[0]) % N(a[1])), hypot: (a) => dbl(Math.hypot(N(a[0]), N(a[1]))),
    gcd: (a) => gcd(a[0], a[1]), __gcd: (a) => gcd(a[0], a[1]),
    lcm: (a) => { const g = gcd(a[0], a[1]); return I.binop('*', I.binop('/', a[0], g), a[1]); },
    isnan: (a) => Number.isNaN(N(a[0])), isinf: (a) => Math.abs(N(a[0])) === Infinity,
    __builtin_popcount: (a) => { let x = N(a[0]) >>> 0, c = 0; while (x) { c += x & 1; x >>>= 1; } return c; },
    __builtin_popcountll: (a) => { let x = BigInt.asUintN(64, BigInt(a[0])), c = 0; while (x) { c += Number(x & 1n); x >>= 1n; } return c; },
    __builtin_clz: (a) => Math.clz32(N(a[0])),
    __builtin_ctz: (a) => { const x = N(a[0]) | 0; return x === 0 ? 32 : 31 - Math.clz32(x & -x); },
    __lg: (a) => 31 - Math.clz32(N(a[0])),
    rand: () => { I.rngState = (Math.imul(I.rngState, 1103515245) + 12345) & 0x7fffffff; return I.rngState; },
    srand: (a) => { I.rngState = N(a[0]) | 0; },
    // ---- conversions / chars
    to_string: (a) => toStringNum(a[0]),
    stoi: (a) => Number(BigInt.asIntN(32, parseIntStr(a[0], a[2] ? N(a[2]) : 10, I.line))), stol: (a) => parseIntStr(a[0], 10, I.line), stoll: (a) => parseIntStr(a[0], 10, I.line), stoul: (a) => Number(parseIntStr(a[0], 10, I.line)), stoull: (a) => parseIntStr(a[0], 10, I.line),
    atoi: (a) => { const m = /^\s*[-+]?\d+/.exec(a[0]); return m ? Number(BigInt.asIntN(32, BigInt(m[0].trim()))) : 0; },
    stod: (a) => dbl(parseFloat(a[0])), stof: (a) => dbl(parseFloat(a[0])), atof: (a) => dbl(parseFloat(a[0]) || 0),
    isdigit: (a) => /[0-9]/.test(chrOf(a[0])), isalpha: (a) => /[A-Za-z]/.test(chrOf(a[0])), isalnum: (a) => /[A-Za-z0-9]/.test(chrOf(a[0])),
    isupper: (a) => /[A-Z]/.test(chrOf(a[0])), islower: (a) => /[a-z]/.test(chrOf(a[0])), isspace: (a) => /\s/.test(chrOf(a[0])), ispunct: (a) => /[!-/:-@[-`{-~]/.test(chrOf(a[0])),
    tolower: (a) => N(a[0]) >= 65 && N(a[0]) <= 90 ? N(a[0]) + 32 : N(a[0]), toupper: (a) => N(a[0]) >= 97 && N(a[0]) <= 122 ? N(a[0]) - 32 : N(a[0]),
    // ---- pairs / tuples / misc
    make_pair: (a) => new Pair(a[0], a[1]),
    make_tuple: (a) => new Tup(a),
    pair: (a) => new Pair(a[0], a[1]),
    get: (a, n) => { const t = a[0]; const k = n.tmplIndex !== undefined ? n.tmplIndex : 0; return t instanceof Pair ? (k ? t.second : t.first) : t.items[k]; },
    move: (a) => a[0], forward: (a) => a[0], ref: (a) => a[0], cref: (a) => a[0],
    exit: () => { throw new RuntimeError('exit() was called', I.line); },
    // ---- output
    printf: (a) => { I.out(I.sprintf(a[0], a.slice(1)), null); return 0; },
    puts: (a) => { I.out(`${a[0]}\n`, null); return 0; },
    putchar: (a) => { I.out(chrOf(a[0]), null); return a[0]; },
    setprecision: (a) => ({ manip: 'setprecision', n: N(a[0]) }),
    setw: (a) => ({ manip: 'setw', n: N(a[0]) }),
    setfill: (a) => ({ manip: 'setfill', c: chrOf(a[0]) }),
    strlen: (a) => a[0].length,
    // ---- algorithms
    sort: (a) => { const r = I.range(a[0], a[1]); sortItems(r.items, lessCmp(a[2])); r.write(r.items); },
    stable_sort: (a) => { const r = I.range(a[0], a[1]); sortItems(r.items, lessCmp(a[2])); r.write(r.items); },
    partial_sort: (a) => { const r = I.range(a[0], a[2]); sortItems(r.items, lessCmp(a[3])); r.write(r.items); },
    reverse: (a) => { const r = I.range(a[0], a[1]); r.items.reverse(); r.write(r.items); },
    fill: (a) => { const r = I.range(a[0], a[1]); const c = toIter(a[0]).coll; const et = Array.isArray(c) && c.et; r.write(r.items.map(() => cloneVal(et ? I.coerce(a[2], et) : a[2]))); },
    fill_n: (a) => { const it = toIter(a[0]); const n = N(a[1]); const end = new Iter(it.coll, it.pos + n); const r = I.range(it, end); r.write(r.items.map(() => a[2])); },
    iota: (a) => { const r = I.range(a[0], a[1]); let v = a[2]; r.write(r.items.map(() => { const x = v; v = I.binop('+', v, 1); return x; })); },
    accumulate: (a) => { const r = I.range(a[0], a[1]); let acc = a[2]; for (const x of r.items) acc = a[3] ? I.callValue(a[3], [acc, x]) : I.binop('+', acc, x); return acc; },
    reduce: (a) => FREE.accumulate(a),
    count: (a) => I.range(a[0], a[1]).items.filter((x) => I.eq(x, a[2])).length,
    count_if: (a) => I.range(a[0], a[1]).items.filter((x) => I.truthy(I.callValue(a[2], [x]))).length,
    find: (a) => { const it = toIter(a[0]); const r = I.range(a[0], a[1]); const i = r.items.findIndex((x) => I.eq(x, a[2])); return i < 0 ? toIter(a[1]) : new Iter(it.coll, it.pos + i, it.keys, it.rev); },
    find_if: (a) => { const it = toIter(a[0]); const r = I.range(a[0], a[1]); const i = r.items.findIndex((x) => I.truthy(I.callValue(a[2], [x]))); return i < 0 ? toIter(a[1]) : new Iter(it.coll, it.pos + i, it.keys, it.rev); },
    all_of: (a) => I.range(a[0], a[1]).items.every((x) => I.truthy(I.callValue(a[2], [x]))),
    any_of: (a) => I.range(a[0], a[1]).items.some((x) => I.truthy(I.callValue(a[2], [x]))),
    none_of: (a) => !I.range(a[0], a[1]).items.some((x) => I.truthy(I.callValue(a[2], [x]))),
    for_each: (a) => { for (const x of I.range(a[0], a[1]).items) I.callValue(a[2], [x]); return a[2]; },
    transform: (a) => { const r = I.range(a[0], a[1]); const out = r.items.map((x) => I.callValue(a[3], [x])); const d = toIter(a[2]); const w = I.range(d, new Iter(d.coll, d.pos + out.length)); w.write(out); },
    copy: (a) => { const r = I.range(a[0], a[1]); const d = toIter(a[2]); const w = I.range(d, new Iter(d.coll, d.pos + r.items.length)); w.write(r.items.map(cloneVal)); },
    lower_bound: (a) => bound(a, true), upper_bound: (a) => bound(a, false),
    binary_search: (a) => { const r = I.range(a[0], a[1]); const c = lessCmp(a[3]); const i = lowerIdx(r.items, a[2], c); return i < r.items.length && !(c ? c(a[2], r.items[i]) < 0 : I.cmpVals(a[2], r.items[i]) < 0); },
    equal_range: (a) => { const lo = bound([a[0], a[1], a[2], a[3]], true); const hi = bound([a[0], a[1], a[2], a[3]], false); return new Pair(lo, hi); },
    max_element: (a) => extreme(a, true), min_element: (a) => extreme(a, false),
    next_permutation: (a) => { const r = I.range(a[0], a[1]); const it = r.items; let i = it.length - 2; while (i >= 0 && I.cmpVals(it[i], it[i + 1]) >= 0) i--; if (i < 0) { it.reverse(); r.write(it); return false; } let j = it.length - 1; while (I.cmpVals(it[j], it[i]) <= 0) j--; [it[i], it[j]] = [it[j], it[i]]; const tail = it.splice(i + 1).reverse(); it.push(...tail); r.write(it); return true; },
    prev_permutation: (a) => { const r = I.range(a[0], a[1]); const it = r.items; let i = it.length - 2; while (i >= 0 && I.cmpVals(it[i], it[i + 1]) <= 0) i--; if (i < 0) { it.reverse(); r.write(it); return false; } let j = it.length - 1; while (I.cmpVals(it[j], it[i]) >= 0) j--; [it[i], it[j]] = [it[j], it[i]]; const tail = it.splice(i + 1).reverse(); it.push(...tail); r.write(it); return true; },
    unique: (a) => { const it = toIter(a[0]); const r = I.range(a[0], a[1]); const out = []; for (const x of r.items) if (!out.length || !(a[2] ? I.truthy(I.callValue(a[2], [out[out.length - 1], x])) : I.eq(out[out.length - 1], x))) out.push(x); const pad = r.items.slice(out.length); r.write([...out, ...pad]); return new Iter(it.coll, it.pos + out.length); },
    remove: (a) => { const it = toIter(a[0]); const r = I.range(a[0], a[1]); const keep = r.items.filter((x) => !I.eq(x, a[2])); r.write([...keep, ...r.items.slice(keep.length)]); return new Iter(it.coll, it.pos + keep.length); },
    remove_if: (a) => { const it = toIter(a[0]); const r = I.range(a[0], a[1]); const keep = r.items.filter((x) => !I.truthy(I.callValue(a[2], [x]))); r.write([...keep, ...r.items.slice(keep.length)]); return new Iter(it.coll, it.pos + keep.length); },
    rotate: (a) => { const r = I.range(a[0], a[2]); const k = toIter(a[1]).pos - toIter(a[0]).pos; r.write([...r.items.slice(k), ...r.items.slice(0, k)]); },
    partial_sum: (a) => { const r = I.range(a[0], a[1]); let acc = null; const out = r.items.map((x) => { acc = acc === null ? x : I.binop('+', acc, x); return acc; }); const d = toIter(a[2]); I.range(d, new Iter(d.coll, d.pos + out.length)).write(out); },
    equal: (a) => { const r = I.range(a[0], a[1]); const d = toIter(a[2]); const r2 = I.range(d, new Iter(d.coll, d.pos + r.items.length)); return r.items.every((x, i) => I.eq(x, r2.items[i])); },
    is_sorted: (a) => { const it = I.range(a[0], a[1]).items; for (let i = 1; i < it.length; i++) if (I.cmpVals(it[i - 1], it[i]) > 0) return false; return true; },
    lexicographical_compare: (a) => I.cmpVals(I.range(a[0], a[1]).items, I.range(a[2], a[3]).items) < 0,
    distance: (a) => toIter(a[1]).pos - toIter(a[0]).pos,
    next: (a) => { const it = toIter(a[0]); return new Iter(it.coll, it.pos + (a[1] === undefined ? 1 : N(a[1])) * (it.rev ? -1 : 1), it.keys, it.rev); },
    prev: (a) => { const it = toIter(a[0]); return new Iter(it.coll, it.pos - (a[1] === undefined ? 1 : N(a[1])) * (it.rev ? -1 : 1), it.keys, it.rev); },
    advance: (a) => { throw new Unsupported('advance() needs an lvalue iterator; use next() instead', I.line); },
    begin: (a) => (Array.isArray(a[0]) ? new Iter(a[0], 0) : I.callMethod(a[0], 'begin', [], null, { line: I.line, args: [] })),
    end: (a) => (Array.isArray(a[0]) ? new Iter(a[0], a[0].length) : I.callMethod(a[0], 'end', [], null, { line: I.line, args: [] })),
    size: (a) => I.callMethod(a[0], 'size', [], null, { line: I.line, args: [] }),
    empty: (a) => I.callMethod(a[0], 'empty', [], null, { line: I.line, args: [] }),
    memcmp: (a) => { const x = a[0], y = a[1]; for (let i = 0; i < Math.min(N(a[2]), x.length); i++) { const c = I.cmpVals(x[i], y[i]); if (c) return c; } return 0; },
    strcmp: (a) => (a[0] < a[1] ? -1 : a[0] > a[1] ? 1 : 0),
    memset: (a) => { memsetFill(a[0], N(a[1]) & 0xFF, N(a[2])); return a[0]; },
    memcpy: (a) => { for (let i = 0; i < a[0].length; i++) a[0][i] = cloneVal(a[1][i]); return a[0]; },
    swap_ranges: (a) => { throw new Unsupported('swap_ranges is not supported', I.line); },
    shuffle: (a) => { const r = I.range(a[0], a[1]); r.write(r.items.reverse()); },
    random_shuffle: (a) => { const r = I.range(a[0], a[1]); r.write(r.items.reverse()); },
    numeric_limits: () => { throw new Unsupported('numeric_limits needs ::max() / ::min()', I.line); },
    pop_heap: () => { throw new Unsupported('Heap functions (make_heap/push_heap/pop_heap) are not supported; use priority_queue', I.line); },
    make_heap: () => { throw new Unsupported('Heap functions (make_heap/push_heap/pop_heap) are not supported; use priority_queue', I.line); },
    push_heap: () => { throw new Unsupported('Heap functions (make_heap/push_heap/pop_heap) are not supported; use priority_queue', I.line); },
    getline: () => { throw new Unsupported('Reading input (getline / cin) is not supported', I.line); },
  };

  function chrOf(x) { return x instanceof Chr ? x.s : typeof x === 'string' ? x : String.fromCharCode(N(x)); }

  function bound(a, lower) {
    const first = toIter(a[0]);
    const r = I.range(a[0], a[1]);
    const c = lessCmp(a[3]);
    const i = lower ? lowerIdx(r.items, a[2], c) : upperIdx(r.items, a[2], c);
    return new Iter(first.coll, first.pos + i, first.keys, first.rev);
  }

  function extreme(a, isMax) {
    const first = toIter(a[0]);
    const r = I.range(a[0], a[1]);
    if (!r.items.length) return toIter(a[1]);
    const c = lessCmp(a[2]) || ((x, y) => I.cmpVals(x, y));
    let bi = 0;
    for (let i = 1; i < r.items.length; i++) { const k = c(r.items[i], r.items[bi]); if (isMax ? k > 0 : k < 0) bi = i; }
    return new Iter(first.coll, first.pos + bi, first.keys, first.rev);
  }

  function memsetFill(arr, byte, nbytes) {
    const flat = [];
    const walk = (x) => { for (let i = 0; i < x.length; i++) { if (Array.isArray(x[i])) walk(x[i]); else flat.push([x, i]); } };
    if (Array.isArray(arr)) walk(arr);
    const et = (arr && arr.et) || null;
    const leaf = (() => { let a = arr; while (Array.isArray(a) && Array.isArray(a[0])) a = a[0]; return a; })();
    const lt = leaf && leaf.et;
    const nm = lt ? lt.name : 'int';
    const size = { int: 4, uint: 4, long: 8, ulong: 8, double: 8, char: 1, uchar: 1, bool: 1, short: 2 }[nm] || 4;
    const count = Math.min(flat.length, Math.floor(nbytes / size));
    const mk = () => {
      switch (nm) {
        case 'long': case 'ulong': { let v = 0n; for (let i = 0; i < 8; i++) v = (v << 8n) | BigInt(byte); return BigInt.asIntN(64, v); }
        case 'double': return dbl(byte === 0 ? 0 : NaN);
        case 'char': case 'uchar': return Chr.of(byte);
        case 'bool': return byte !== 0;
        case 'short': return ((byte << 8) | byte) << 16 >> 16;
        default: return ((byte << 24) | (byte << 16) | (byte << 8) | byte) | 0;
      }
    };
    void et;
    for (let k = 0; k < count; k++) { const [x, i] = flat[k]; x[i] = mk(); }
  }

  I.callBuiltinValues = function callBuiltinValues(name, args, line) {
    const f = FREE[name];
    if (f) { I.line = line || I.line; return f(args, {}); }
    throw new RuntimeError(`The function "${name}" is not supported by the visualizer`, line);
  };

  I.callBuiltinNode = function callBuiltinNode(name, n) {
    const line = n.line;
    if (name in FREE_LV) {
      const lv = FREE_LV[name];
      if (name === 'tie') return lv(n.args.map((a) => (a.k === 'id' && a.name === 'ignore' ? null : I.evalLv(a))));
      if (name === 'iter_swap') return lv(n.args.map((a) => I.evalExpr(a)));
      return lv(n.args.map((a) => I.evalLv(a)));
    }
    const f = FREE[name];
    if (!f) {
      if (I.lang === 'cpp' && /^(cin|scanf|getchar|gets)$/.test(name)) throw new Unsupported('Reading input is not supported', line);
      throw new RuntimeError(`The function "${name}" is not defined (or not supported by the visualizer)`, line);
    }
    // get<N>(tuple): template index lives on the callee's `construct` form; handled by evalCall's callee being `id`
    const args = n.args.map((a) => (a.k === 'initlist' ? I.evalAny(a) : I.evalExpr(a)));
    I.line = line;
    return f(args, n);
  };

  // ------------------------------------------------------------ static classes (Java + C++ helpers)
  I.callStaticBuiltin = function callStaticBuiltin(cname, name, n, typeNode) {
    const line = n.line;
    I.line = line;
    // numeric_limits<T>::max()
    if (cname === 'numeric_limits' || (typeNode && typeNode.name === 'numeric_limits')) {
      const t = (typeNode || n.callee.left.type).args[0];
      const tn = I.resolveType(t).name;
      const lim = NUMLIM[tn];
      if (name === 'max') return lim ? lim[1] : dbl(Number.MAX_VALUE);
      if (name === 'min') return lim ? lim[0] : dbl(2.2250738585072014e-308);
      if (name === 'lowest') return lim ? lim[0] : dbl(-Number.MAX_VALUE);
      if (name === 'infinity') return dbl(Infinity);
      if (name === 'epsilon') return dbl(Number.EPSILON);
    }
    const argc = n.args.length;
    const args = n.args.map((a) => (a.k === 'initlist' ? I.evalAny(a) : I.evalExpr(a)));
    const num = (x) => N(x);
    const J = {
      Math: {
        abs: () => absf(args[0]), max: () => maxmin(true)(args), min: () => maxmin(false)(args),
        pow: () => dbl(Math.pow(num(args[0]), num(args[1]))), sqrt: () => dbl(Math.sqrt(num(args[0]))), cbrt: () => dbl(Math.cbrt(num(args[0]))),
        floor: () => dbl(Math.floor(num(args[0]))), ceil: () => dbl(Math.ceil(num(args[0]))), rint: () => dbl(Math.round(num(args[0]))),
        round: () => BigInt(Math.floor(num(args[0]) + 0.5)), log: () => dbl(Math.log(num(args[0]))), log10: () => dbl(Math.log10(num(args[0]))), exp: () => dbl(Math.exp(num(args[0]))),
        sin: () => dbl(Math.sin(num(args[0]))), cos: () => dbl(Math.cos(num(args[0]))), tan: () => dbl(Math.tan(num(args[0]))), atan: () => dbl(Math.atan(num(args[0]))), atan2: () => dbl(Math.atan2(num(args[0]), num(args[1]))), hypot: () => dbl(Math.hypot(num(args[0]), num(args[1]))),
        signum: () => dbl(Math.sign(num(args[0]))), random: () => { I.rngState = (Math.imul(I.rngState, 1103515245) + 12345) & 0x7fffffff; return dbl(I.rngState / 2147483648); },
        floorMod: () => { const a = args[0], b = args[1]; if (typeof a === 'bigint' || typeof b === 'bigint') { const x = BigInt(a), y = BigInt(b); return ((x % y) + y) % y; } if (b === 0) throw I.divZero(); return ((a % b) + b) % b; },
        floorDiv: () => { const a = args[0], b = args[1]; if (typeof a === 'bigint' || typeof b === 'bigint') { const x = BigInt(a), y = BigInt(b); let q = x / y; if ((x % y !== 0n) && ((x < 0n) !== (y < 0n))) q -= 1n; return q; } if (b === 0) throw I.divZero(); return Math.floor(a / b); },
        addExact: () => exact('+'), subtractExact: () => exact('-'), multiplyExact: () => exact('*'), toIntExact: () => { const v = BigInt(args[0]); if (v > 2147483647n || v < -2147483648n) { const e = new RuntimeError('ArithmeticException: integer overflow', line); e.exc = 'ArithmeticException'; throw e; } return Number(v); },
        negateExact: () => -args[0], toRadians: () => dbl(num(args[0]) * Math.PI / 180), toDegrees: () => dbl(num(args[0]) * 180 / Math.PI),
      },
      Integer: {
        parseInt: () => Number(BigInt.asIntN(32, parseIntStr(args[0], argc > 1 ? num(args[1]) : 10, line))), valueOf: () => (typeof args[0] === 'string' ? Number(parseIntStr(args[0], 10, line)) : I.coerce(args[0], { name: 'int', ptr: 0 })),
        toString: () => (argc > 1 ? (num(args[0]) >>> 0 === num(args[0]) || num(args[0]) >= 0 ? num(args[0]).toString(num(args[1])) : (-num(args[0])).toString(num(args[1])).replace(/^/, '-')) : String(args[0])),
        max: () => maxmin(true)(args), min: () => maxmin(false)(args), sum: () => I.binop('+', args[0], args[1]), compare: () => Math.sign(num(args[0]) - num(args[1])),
        signum: () => Math.sign(num(args[0])), bitCount: () => FREE.__builtin_popcount(args), toBinaryString: () => (num(args[0]) >>> 0).toString(2), toHexString: () => (num(args[0]) >>> 0).toString(16), toOctalString: () => (num(args[0]) >>> 0).toString(8),
        highestOneBit: () => (num(args[0]) === 0 ? 0 : (1 << (31 - Math.clz32(num(args[0])))) | 0), numberOfTrailingZeros: () => FREE.__builtin_ctz(args), numberOfLeadingZeros: () => Math.clz32(num(args[0])), reverse: () => { let x = num(args[0]) >>> 0, r = 0; for (let i = 0; i < 32; i++) { r = (r << 1) | (x & 1); x >>>= 1; } return r | 0; },
        hashCode: () => V.javaHash(args[0]), abs: () => absf(args[0]),
      },
      Long: {
        parseLong: () => parseIntStr(args[0], 10, line), valueOf: () => (typeof args[0] === 'string' ? parseIntStr(args[0], 10, line) : I.toLong(args[0])), toString: () => String(args[0]), max: () => maxmin(true)(args), min: () => maxmin(false)(args), sum: () => I.binop('+', I.toLong(args[0]), args[1]),
        compare: () => (BigInt(args[0]) < BigInt(args[1]) ? -1 : BigInt(args[0]) > BigInt(args[1]) ? 1 : 0), signum: () => Math.sign(num(args[0])), bitCount: () => FREE.__builtin_popcountll(args), hashCode: () => V.javaHash(I.toLong(args[0])),
        numberOfTrailingZeros: () => { let x = BigInt.asUintN(64, BigInt(args[0])); if (!x) return 64; let c = 0; while (!(x & 1n)) { x >>= 1n; c++; } return c; }, toBinaryString: () => BigInt.asUintN(64, BigInt(args[0])).toString(2), abs: () => absf(args[0]),
      },
      Double: { parseDouble: () => dbl(parseFloat(args[0])), valueOf: () => (typeof args[0] === 'string' ? dbl(parseFloat(args[0])) : dbl(num(args[0]))), toString: () => javaDouble(num(args[0])), compare: () => Math.sign(num(args[0]) - num(args[1])), isNaN: () => Number.isNaN(num(args[0])), isInfinite: () => Math.abs(num(args[0])) === Infinity, max: () => maxmin(true)(args), min: () => maxmin(false)(args), sum: () => dbl(num(args[0]) + num(args[1])) },
      Boolean: { parseBoolean: () => String(args[0]).toLowerCase() === 'true', valueOf: () => (typeof args[0] === 'string' ? args[0].toLowerCase() === 'true' : args[0]), toString: () => String(args[0]) },
      Character: {
        isDigit: () => /[0-9]/.test(chrOf(args[0])), isLetter: () => /\p{L}/u.test(chrOf(args[0])), isLetterOrDigit: () => /[\p{L}0-9]/u.test(chrOf(args[0])), isAlphabetic: () => /\p{L}/u.test(chrOf(args[0])),
        isUpperCase: () => /\p{Lu}/u.test(chrOf(args[0])), isLowerCase: () => /\p{Ll}/u.test(chrOf(args[0])), isWhitespace: () => /\s/.test(chrOf(args[0])), isSpaceChar: () => /\s/.test(chrOf(args[0])),
        toUpperCase: () => (args[0] instanceof Chr ? Chr.from(args[0].s.toUpperCase()) : String.fromCharCode(num(args[0])).toUpperCase().charCodeAt(0)), toLowerCase: () => (args[0] instanceof Chr ? Chr.from(args[0].s.toLowerCase()) : String.fromCharCode(num(args[0])).toLowerCase().charCodeAt(0)),
        getNumericValue: () => { const c = chrOf(args[0]); return /[0-9]/.test(c) ? c.charCodeAt(0) - 48 : /[a-zA-Z]/.test(c) ? c.toLowerCase().charCodeAt(0) - 87 : -1; }, valueOf: () => args[0], toString: () => chrOf(args[0]), compare: () => num(args[0]) - num(args[1]), hashCode: () => num(args[0]),
        forDigit: () => Chr.from((num(args[0])).toString(num(args[1]))), digit: () => { const v = parseInt(chrOf(args[0]), num(args[1])); return Number.isNaN(v) ? -1 : v; },
      },
      String: {
        valueOf: () => (Array.isArray(args[0]) ? args[0].map(chrOf).join('') : I.str(args[0])), copyValueOf: () => args[0].map(chrOf).join(''), join: () => { const d = I.str(args[0]); const rest = argc === 2 && (Array.isArray(args[1]) || args[1] instanceof SetObj || args[1] instanceof Seq) ? (Array.isArray(args[1]) ? args[1] : args[1] instanceof Seq ? args[1].a : args[1].keys()) : args.slice(1); return rest.map((x) => I.str(x)).join(d); },
        format: () => I.sprintf(args[0], args.slice(1), true),
      },
      Arrays: {
        toString: () => (args[0] === null ? 'null' : `[${args[0].map((x) => I.str(x)).join(', ')}]`), deepToString: () => { const f = (x) => (Array.isArray(x) ? `[${x.map(f).join(', ')}]` : I.str(x)); return f(args[0]); },
        sort: () => { const a = args[0]; let lo = 0, hi = a.length, cmp = null; if (argc === 2) cmp = args[1]; if (argc >= 3) { lo = num(args[1]); hi = num(args[2]); if (argc === 4) cmp = args[3]; } const part = a.slice(lo, hi); sortItems(part, cmp ? I.makeCmp(cmp) : null); for (let i = 0; i < part.length; i++) a[lo + i] = part[i]; },
        fill: () => { const a = args[0]; if (argc === 2) for (let i = 0; i < a.length; i++) a[i] = cloneVal(I.coerce(args[1], a.et)); else for (let i = num(args[1]); i < num(args[2]); i++) a[i] = I.coerce(args[3], a.et); },
        asList: () => { const a = argc === 1 && Array.isArray(args[0]) ? args[0].slice() : args.slice(); return a; },
        copyOf: () => { const a = args[0]; const n = num(args[1]); const out = a.slice(0, n); out.et = a.et; while (out.length < n) out.push(I.defaultValue(a.et || { name: 'int', args: [], ptr: 0, dims: 0 })); return out; },
        copyOfRange: () => { const a = args[0]; const out = a.slice(num(args[1]), num(args[2])); out.et = a.et; while (out.length < num(args[2]) - num(args[1])) out.push(I.defaultValue(a.et || { name: 'int', args: [], ptr: 0, dims: 0 })); return out; },
        equals: () => equals(args[0], args[1]), deepEquals: () => equals(args[0], args[1]), hashCode: () => V.javaHash(args[0]),
        binarySearch: () => { const a = args[0]; let lo = 0, hi = a.length - 1; const key = args[argc === 2 ? 1 : 3]; if (argc >= 3) { lo = num(args[1]); hi = num(args[2]) - 1; } while (lo <= hi) { const m = (lo + hi) >>> 1; const c = I.cmpVals(a[m], key); if (c < 0) lo = m + 1; else if (c > 0) hi = m - 1; else return m; } return -(lo + 1); },
        stream: () => { throw new Unsupported('Java streams are not supported by the visualizer', line); }, setAll: () => { throw new Unsupported('Arrays.setAll is not supported', line); },
      },
      Collections: {
        sort: () => { const a = args[0] instanceof Seq ? args[0].a : args[0]; sortItems(a, argc > 1 ? I.makeCmp(args[1]) : null); }, reverse: () => { (args[0] instanceof Seq ? args[0].a : args[0]).reverse(); },
        max: () => { const a = args[0] instanceof SetObj ? args[0].keys() : args[0] instanceof Seq ? args[0].a : args[0]; if (!a.length) { const e = new RuntimeError('NoSuchElementException', line); e.exc = 'NoSuchElementException'; throw e; } const c = argc > 1 ? I.makeCmp(args[1]) : (x, y) => I.cmpVals(x, y); return a.reduce((b, x) => (c(x, b) > 0 ? x : b)); },
        min: () => { const a = args[0] instanceof SetObj ? args[0].keys() : args[0] instanceof Seq ? args[0].a : args[0]; if (!a.length) { const e = new RuntimeError('NoSuchElementException', line); e.exc = 'NoSuchElementException'; throw e; } const c = argc > 1 ? I.makeCmp(args[1]) : (x, y) => I.cmpVals(x, y); return a.reduce((b, x) => (c(x, b) < 0 ? x : b)); },
        swap: () => { const a = args[0]; const i = num(args[1]), j = num(args[2]); I.checkIndex(i, a.length, line, 'list'); I.checkIndex(j, a.length, line, 'list'); [a[i], a[j]] = [a[j], a[i]]; },
        unmodifiableList: () => args[0], unmodifiableSet: () => args[0], unmodifiableMap: () => args[0], synchronizedList: () => args[0], emptyList: () => [], emptyMap: () => new MapObj('map', false), emptySet: () => new SetObj('set', false), singletonList: () => [args[0]], singleton: () => { const s = new SetObj('set', false); I.setAdd(s, args[0]); return s; },
        reverseOrder: () => (argc ? new FnRef((x) => -I.makeCmp(args[0])(x[0], x[1]), 'reverseOrder') : new FnRef((x) => I.cmpVals(x[1], x[0]), 'reverseOrder')),
        frequency: () => (Array.isArray(args[0]) ? args[0] : args[0].a || args[0].keys()).filter((x) => I.eq(x, args[1])).length, nCopies: () => { const a = []; for (let i = 0; i < num(args[0]); i++) a.push(args[1]); return a; },
        addAll: () => { for (const x of args.slice(1)) { if (args[0] instanceof SetObj) I.setAdd(args[0], x); else args[0].push(x); } return true; }, shuffle: () => { args[0].reverse(); }, fill: () => { for (let i = 0; i < args[0].length; i++) args[0][i] = args[1]; },
        binarySearch: () => J.Arrays.binarySearch(),
      },
      List: { of: () => { const a = args.slice(); return a; }, copyOf: () => args[0].slice() },
      Set: { of: () => { const s = new SetObj('set', false); s.jhash = true; for (const x of args) I.setAdd(s, x); return s; }, copyOf: () => { const s = new SetObj('set', false); for (const x of args[0].keys()) I.setAdd(s, x); return s; } },
      Map: { of: () => { const m = new MapObj('umap', false); m.jhash = true; for (let i = 0; i + 1 < args.length; i += 2) I.mapPut(m, args[i], args[i + 1]); return m; }, entry: () => new Pair(args[0], args[1]), copyOf: () => args[0] },
      Entry: { comparingByKey: () => new FnRef((x) => I.cmpVals(x[0].first, x[1].first), 'cmpKey'), comparingByValue: () => new FnRef((x) => I.cmpVals(x[0].second, x[1].second), 'cmpVal') },
      Objects: { equals: () => I.eq(args[0], args[1]), hash: () => V.javaHash(args), hashCode: () => V.javaHash(args[0]), requireNonNull: () => { if (args[0] === null) { const e = new RuntimeError('NullPointerException', line); e.exc = 'NullPointerException'; throw e; } return args[0]; }, toString: () => I.str(args[0]), isNull: () => args[0] === null, nonNull: () => args[0] !== null },
      System: { currentTimeMillis: () => 0n, nanoTime: () => 0n, exit: () => { throw new RuntimeError('System.exit() was called', line); }, arraycopy: () => { const [src, sp, dst, dp, len] = [args[0], num(args[1]), args[2], num(args[3]), num(args[4])]; if (sp < 0 || dp < 0 || len < 0 || sp + len > src.length || dp + len > dst.length) { const e = new RuntimeError('ArrayIndexOutOfBoundsException: arraycopy: last source index out of bounds', line); e.exc = 'ArrayIndexOutOfBoundsException'; throw e; } const tmp = src.slice(sp, sp + len); for (let i = 0; i < len; i++) dst[dp + i] = tmp[i]; }, lineSeparator: () => '\n', identityHashCode: () => 0, getProperty: () => null },
      Comparator: {
        comparingInt: () => new FnRef((x) => I.cmpVals(I.callValue(args[0], [x[0]]), I.callValue(args[0], [x[1]])), 'cmp'), comparingLong: () => new FnRef((x) => I.cmpVals(I.callValue(args[0], [x[0]]), I.callValue(args[0], [x[1]])), 'cmp'), comparingDouble: () => new FnRef((x) => I.cmpVals(I.callValue(args[0], [x[0]]), I.callValue(args[0], [x[1]])), 'cmp'),
        comparing: () => new FnRef((x) => { const ka = I.callValue(args[0], [x[0]]), kb = I.callValue(args[0], [x[1]]); return argc > 1 ? I.makeCmp(args[1])(ka, kb) : I.cmpVals(ka, kb); }, 'cmp'),
        naturalOrder: () => new FnRef((x) => I.cmpVals(x[0], x[1]), 'natural'), reverseOrder: () => new FnRef((x) => I.cmpVals(x[1], x[0]), 'reverse'),
      },
      Thread: { sleep: () => undefined },
    };
    if (cname === 'Float') return J.Double[name] ? J.Double[name]() : undefined;
    if (cname === 'Short' || cname === 'Byte') return J.Integer[name] ? J.Integer[name]() : undefined;
    if (cname === 'Stream' || cname === 'IntStream' || cname === 'Collectors') throw new Unsupported('Java streams are not supported by the visualizer', line);
    if (cname === 'BigInteger' || cname === 'BigDecimal') throw new Unsupported(`${cname} is not supported by the visualizer`, line);
    const tbl = J[cname];
    if (tbl && tbl[name]) return tbl[name]();
    if (cname === 'std' || cname === 'ranges') return I.callBuiltinNode(name, n);
    if (this.classes[cname] && this.classes[cname].kind === 'enum') {
      const c = this.classes[cname];
      if (!c.staticInitDone) I.initStatics(c);
      if (name === 'values') return Object.values(c.enumConsts);
      if (name === 'valueOf') { const o = c.enumConsts[args[0]]; if (!o) { const e = new RuntimeError(`IllegalArgumentException: No enum constant ${cname}.${args[0]}`, line); e.exc = 'IllegalArgumentException'; throw e; } return o; }
    }
    throw new RuntimeError(`${cname}.${name}() is not supported by the visualizer`, line);

    function exact(op) {
      const a = args[0], b = args[1];
      const big = typeof a === 'bigint' || typeof b === 'bigint';
      const x = BigInt(a), y = BigInt(b);
      const r = op === '+' ? x + y : op === '-' ? x - y : x * y;
      const lim = big ? [L_MIN, L_MAX] : [BigInt(I32_MIN), BigInt(I32_MAX)];
      if (r < lim[0] || r > lim[1]) { const e = new RuntimeError(`ArithmeticException: ${big ? 'long' : 'integer'} overflow`, line); e.exc = 'ArithmeticException'; throw e; }
      return big ? r : Number(r);
    }
  };
}
