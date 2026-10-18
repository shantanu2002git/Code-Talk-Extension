// Empirical cross-check of a static bound: run the code on generated inputs of growing size, count the interpreter's
// operations, and compare the growth with the claimed bound. A measurement can REFUTE a claim (so we withhold it); it never
// produces a claim by itself.
import * as A from './algebra.js';

function rng(seed) { let s = seed >>> 0 || 1; return () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; }; }

/** which parameters scale, according to the analysis' symbols */
function specOf(an, fn) {
  const spec = {};
  for (const [key] of an.psyms) { const [kind, name] = key.split(/:(.*)/); if (fn.params.some((p) => p.n === name)) (spec[name] = spec[name] || {})[kind] = true; }
  return spec;
}

function gen(ty, sp, N, rnd, depth = 0) {
  switch (ty.k) {
    case 'int': return sp.val ? N : Math.floor(rnd() * 8) + 1;
    case 'float': return sp.val ? N : 1.5;
    case 'bool': return rnd() < 0.5;
    case 'str': return Array.from({ length: sp.len ? N : 6 }, () => 'abc'[Math.floor(rnd() * 3)]).join('');
    case 'list': case 'array': {
      const e = ty.e || { k: 'int' };
      const n = depth === 0 ? (sp.len || sp.nodes || sp.E ? N : 6) : (sp.row ? N : Math.floor(rnd() * 3) + 1);
      if (e.k === 'list' || e.k === 'array') {
        // graph-like (E but no row length) stays sparse; matrices are N x N
        const rows = sp.len || sp.E ? N : 4;
        const sparse = sp.E && !sp.row;
        return Array.from({ length: rows }, () => gen(e, sparse ? { len: false, row: false, val: false, sparseN: N } : { row: true }, N, rnd, depth + 1));
      }
      if (e.k === 'int' && sp.sparseN) return Array.from({ length: Math.floor(rnd() * 3) }, () => Math.floor(rnd() * sp.sparseN));
      if (e.k === 'int' && e.name === 'char') return Array.from({ length: n }, () => '01'[Math.floor(rnd() * 2)]);
      if (e.k === 'str') return Array.from({ length: n }, () => gen(e, { len: false }, N, rnd, depth + 1));
      return Array.from({ length: n }, () => (e.k === 'int' ? Math.floor(rnd() * Math.max(N, 10)) : gen(e, {}, N, rnd, depth + 1)));
    }
    case 'tree': return Array.from({ length: sp.nodes || sp.h ? N : 7 }, () => Math.floor(rnd() * 100));
    case 'node': return Array.from({ length: sp.nodes ? N : 5 }, () => Math.floor(rnd() * 100));
    default: throw new Error(`cannot generate an input for type ${ty.k}`);
  }
}

export function genArgs(an, fn, N, seed = 7) {
  const rnd = rng(seed + N);
  const spec = specOf(an, fn);
  return fn.params.map((p) => {
    const ty = p.ty && p.ty.k !== 'unknown' ? p.ty : an.inferParamType(p, fn);
    return gen(ty, spec[p.n] || {}, N, rnd, 0);
  });
}

const treeHeight = (a) => { // level-order array with nulls: complete-tree approximation when no nulls
  const n = a.filter((x) => x !== null).length; return Math.floor(Math.log2(Math.max(n, 1))) + 1;
};

/** numeric values of the analysis symbols for concrete arguments */
export function symValues(an, fn, args) {
  const vals = {};
  for (const [key, s] of an.psyms) {
    const [kind, name] = key.split(/:(.*)/);
    const idx = fn.params.findIndex((p) => p.n === name);
    if (idx < 0) continue;
    const a = args[idx]; const id = Object.keys(s[0].p)[0];
    let v = 1;
    if (kind === 'len') v = Array.isArray(a) || typeof a === 'string' ? a.length : 1;
    else if (kind === 'val') v = typeof a === 'number' ? a : 1;
    else if (kind === 'row') v = Array.isArray(a) && Array.isArray(a[0]) ? a[0].length : 1;
    else if (kind === 'nodes') v = Array.isArray(a) ? a.filter((x) => x !== null).length : 1;
    else if (kind === 'h') v = Array.isArray(a) ? treeHeight(a) : 1;
    else if (kind === 'E') v = Array.isArray(a) ? a.reduce((t, r) => t + (Array.isArray(r) ? r.length : 1), 0) : 1;
    else if (kind === 'max') v = Array.isArray(a) ? Math.max(1, ...a.filter((x) => typeof x === 'number')) : 1;
    else if (kind === 'sum') v = Array.isArray(a) ? a.reduce((t, x) => t + (typeof x === 'number' ? x : 0), 0) : 1;
    vals[id] = Math.max(1, v);
  }
  return vals;
}

/** run the measurement. runOps(args) -> Promise<{ok, ops}> */
export async function measure(an, result, runOps, { sizes = null, budget = 6 } = {}) {
  const fn = result.fn;
  const fast = result.time.some((t) => t.x || t.f);
  const Ns = sizes || (fast ? [3, 5, 7, 9] : [16, 32, 64, 128]);
  const pts = [];
  for (const N of Ns.slice(0, budget)) {
    let args;
    try { args = genArgs(an, fn, N); } catch (e) { return { status: 'unavailable', reason: e.message }; }
    const out = await runOps(args);
    if (!out || !out.ok) { if (pts.length >= 2) break; return { status: 'unavailable', reason: out && out.error ? out.error : 'the generated input could not be run' }; }
    const vals = symValues(an, fn, args);
    pts.push({ N, ops: out.ops, pred: A.evalE(result.time, vals), vals });
  }
  if (pts.length < 3) return { status: 'unavailable', reason: 'too few successful runs', points: pts };
  const r0 = pts[0].ops / pts[0].pred, r1 = pts[pts.length - 1].ops / pts[pts.length - 1].pred;
  const g = r1 / r0;
  if (g > 3) return { status: 'contradiction', growth: g, points: pts };
  if (g < 0.2) return { status: 'looser', growth: g, points: pts };
  return { status: 'consistent', growth: g, points: pts };
}
