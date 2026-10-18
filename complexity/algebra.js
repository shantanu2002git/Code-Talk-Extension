// Asymptotic algebra for Big-O expressions in several size symbols.
// A term is  Π sym^p · Π (log sym)^l · base^sym · sym!   (constants are dropped: Big-O).
// Everything here is exact symbolic bookkeeping; nothing is estimated.

const key = (t) => JSON.stringify([Object.entries(t.p).sort(), Object.entries(t.l).sort(), t.x ? Object.entries(t.x).sort() : [], t.f ? [...t.f].sort() : []]);
const clean = (o) => { const r = {}; for (const [k, v] of Object.entries(o || {})) if (v) r[k] = v; return r; };

export const ONE = [{ p: {}, l: {}, x: null, f: null }];
export const mkTerm = (p = {}, l = {}, x = null, f = null) => ({ p: clean(p), l: clean(l), x: x && Object.keys(x).length ? { ...x } : null, f: f && f.length ? [...f] : null });
export const sym = (id) => [mkTerm({ [id]: 1 })];
export const isOne = (e) => e.length === 1 && !Object.keys(e[0].p).length && !Object.keys(e[0].l).length && !e[0].x && !e[0].f;

// growth rank of a term restricted to one symbol: tuple compared lexicographically
function rank(t, s) {
  const fact = t.f && t.f.includes(s) ? 1 : 0;
  const ex = t.x && t.x[s] ? Math.log(t.x[s]) : 0;
  return [fact, ex, t.p[s] || 0, t.l[s] || 0];
}
function cmpRank(a, b) { for (let i = 0; i < 4; i++) { if (a[i] !== b[i]) return a[i] < b[i] ? -1 : 1; } return 0; }
function symsOf(t) { return new Set([...Object.keys(t.p), ...Object.keys(t.l), ...(t.x ? Object.keys(t.x) : []), ...(t.f || [])]); }
/** true when a grows at least as fast as b for every symbol (so b can be dropped from a sum) */
export function dominates(a, b, order) {
  const syms = new Set([...symsOf(a), ...symsOf(b)]);
  for (const s of syms) {
    let ra = rank(a, s), rb = rank(b, s);
    if (cmpRank(ra, rb) < 0) {
      // a symbol that is provably <= another one (height <= nodes) may be traded
      return false;
    }
  }
  void order;
  return true;
}

export function add(a, b, le = null) {
  const all = [...a, ...b];
  const out = [];
  for (const t of all) {
    if (out.some((u) => dominates(substLe(u, le), substLe(t, le)) && key(u) !== key(t) ? true : key(u) === key(t))) continue;
    for (let i = out.length - 1; i >= 0; i--) if (dominates(substLe(t, le), substLe(out[i], le))) out.splice(i, 1);
    out.push(t);
  }
  return out.length ? out : ONE;
}
// le: map sym -> sym it is <= (e.g. h -> n); used only for comparing, never for printing
function substLe(t, le) {
  if (!le) return t;
  const p = { ...t.p };
  for (const [s, big] of Object.entries(le)) if (p[s]) { p[big] = Math.max(p[big] || 0, p[s]); delete p[s]; }
  return { ...t, p };
}
export const maxE = add;

export function mulTerm(a, b) {
  const p = { ...a.p }, l = { ...a.l };
  for (const [k, v] of Object.entries(b.p)) p[k] = (p[k] || 0) + v;
  for (const [k, v] of Object.entries(b.l)) l[k] = (l[k] || 0) + v;
  let x = a.x ? { ...a.x } : null;
  if (b.x) { x = x || {}; for (const [k, v] of Object.entries(b.x)) x[k] = x[k] ? x[k] * v : v; }
  const f = [...(a.f || []), ...(b.f || [])];
  return mkTerm(p, l, x, f);
}
export function mul(a, b, le = null) {
  let out = [];
  for (const x of a) for (const y of b) out = add(out, [mulTerm(x, y)], le);
  return out;
}
export function pow(e, k) { let r = ONE; for (let i = 0; i < k; i++) r = mul(r, e); return r; }
export function logE(e) {
  let out = [];
  for (const t of e) {
    if (t.x) { // log(c^n) = n
      for (const s of Object.keys(t.x)) out = add(out, [mkTerm({ [s]: 1 })]);
      continue;
    }
    if (t.f) { for (const s of t.f) out = add(out, [mkTerm({ [s]: 1 }, { [s]: 1 })]); continue; }
    const ss = Object.keys(t.p);
    if (!ss.length) { out = add(out, ONE); continue; }
    for (const s of ss) out = add(out, [mkTerm({}, { [s]: 1 })]);
  }
  return out.length ? out : ONE;
}
export function sqrtE(e) {
  if (e.length !== 1 || e[0].x || e[0].f) return null;
  const t = e[0]; const p = {};
  for (const [k, v] of Object.entries(t.p)) p[k] = v / 2;
  return [mkTerm(p, t.l)];
}
export function expE(base, e) { // base^e where e is a single linear symbol term
  if (e.length !== 1 || e[0].x || e[0].f || e[0].l && Object.keys(e[0].l).length) return null;
  const ks = Object.keys(e[0].p);
  if (ks.length !== 1 || e[0].p[ks[0]] !== 1) return null;
  return [mkTerm({}, {}, { [ks[0]]: base })];
}
export function factE(e) {
  if (e.length !== 1 || e[0].x || e[0].f) return null;
  const ks = Object.keys(e[0].p);
  if (ks.length !== 1 || e[0].p[ks[0]] !== 1) return null;
  return [mkTerm({}, {}, null, [ks[0]])];
}
export const eq = (a, b) => a.length === b.length && a.every((t) => b.some((u) => key(t) === key(u)));
export function symbolsIn(e) { const s = new Set(); for (const t of e) for (const x of symsOf(t)) s.add(x); return s; }
export function degreeIn(e, s) { return e.reduce((m, t) => Math.max(m, t.p[s] || 0), 0); }
export function hasExpOrFact(e) { return e.some((t) => t.x || t.f); }
/** substitute symbol s by expression r in e (used for loop variables bounded by an outer expression) */
export function subst(e, s, r) {
  let out = [];
  for (const t of e) {
    const k = t.p[s] || 0;
    if (!k) { out = add(out, [t]); continue; }
    const rest = mkTerm({ ...t.p, [s]: 0 }, t.l, t.x, t.f);
    out = add(out, mul([rest], pow(r, k)));
  }
  return out.length ? out : ONE;
}

// ---------------------------------------------------------------- printing
const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹', '.': '·', '-': '⁻' };
const sup = (n) => String(n).split('').map((c) => SUP[c] || c).join('');
export function fmtTerm(t, name) {
  const parts = [];
  if (t.f) for (const s of t.f) parts.push(`${name(s)}!`);
  if (t.x) for (const [s, b] of Object.entries(t.x)) parts.push(`${b === Math.E ? 'e' : String(b)}^${name(s)}`.replace(/\^(.+)$/, (m, v) => (v.length === 1 ? sup(v) === v ? `^${v}` : `^${v}` : `^(${v})`)));
  for (const [s, p] of Object.entries(t.p)) parts.push(p === 0.5 ? `√${name(s)}` : p === 1 ? name(s) : `${name(s)}${sup(p)}`);
  for (const [s, p] of Object.entries(t.l)) parts.push(p === 1 ? `log ${name(s)}` : `log${sup(p)} ${name(s)}`);
  return parts.length ? parts.join(' · ').replace(/ · log/g, ' log') : '1';
}
export function fmt(e, name = (s) => s) {
  const ts = e.map((t) => fmtTerm(t, name));
  return `O(${ts.join(' + ')})`;
}

/** numeric value of an expression for given symbol values (illustration only; constants are ignored in Big-O) */
export function evalE(e, vals) {
  let total = 0;
  for (const t of e) {
    let v = 1;
    for (const [s, p] of Object.entries(t.p)) v *= Math.pow(Math.max(vals[s] ?? 1, 1), p);
    for (const [s, p] of Object.entries(t.l)) v *= Math.pow(Math.max(Math.log2(Math.max(vals[s] ?? 2, 2)), 1), p);
    if (t.x) for (const [s, b] of Object.entries(t.x)) v *= Math.pow(b, Math.max(vals[s] ?? 1, 0));
    if (t.f) for (const s of t.f) { let f = 1; for (let i = 2; i <= Math.min(vals[s] ?? 1, 170); i++) f *= i; v *= f; }
    total += v;
  }
  return total;
}

/** a grows at least as fast as b (every term of b is dominated by a term of a) */
export function geq(a, b) { return b.every((tb) => a.some((ta) => dominates(ta, tb))); }
