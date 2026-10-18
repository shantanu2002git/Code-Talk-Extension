// Small helpers over the IR: traversal, structural equality, printing of expressions.
export class Und extends Error {
  constructor(reason, line = null, hint = '') { super(reason); this.reason = reason; this.line = line; this.hint = hint; }
}

export const isId = (e, n) => e && e.t === 'id' && (n === undefined || e.n === n);
export const isNum = (e) => e && e.t === 'num';

/** Visit every sub-expression of an expression (pre-order). */
export function eachExpr(e, f) {
  if (!e || typeof e !== 'object') return;
  f(e);
  switch (e.t) {
    case 'op': case 'lit': e.a.forEach((x) => eachExpr(x, f)); break;
    case 'call': if (e.recv) eachExpr(e.recv, f); e.a.forEach((x) => eachExpr(x, f)); break;
    case 'idx': eachExpr(e.o, f); eachExpr(e.i, f); break;
    case 'slice': eachExpr(e.o, f); eachExpr(e.lo, f); eachExpr(e.hi, f); eachExpr(e.step, f); break;
    case 'attr': eachExpr(e.o, f); break;
    case 'new': e.a.forEach((x) => eachExpr(x, f)); if (e.init) eachExpr(e.init, f); break;
    case 'assign': eachExpr(e.target, f); eachExpr(e.v, f); break;
    case 'incdec': eachExpr(e.target, f); break;
    case 'comp': e.gens.forEach((g) => eachExpr(g.iter, f)); e.conds.forEach((x) => eachExpr(x, f)); eachExpr(e.elt, f); break;
    case 'lambda': eachStmtExprs(e.body, f); break;
    case 'tuple': e.a.forEach((x) => eachExpr(x, f)); break;
    default: break;
  }
}

/** Visit every statement (pre-order); `f(stmt, parentStmts)` */
export function eachStmt(stmts, f, parents = []) {
  for (const s of stmts || []) {
    f(s, parents);
    const p = [...parents, s];
    switch (s.s) {
      case 'if': eachStmt(s.then, f, p); eachStmt(s.else, f, p); break;
      case 'for': case 'while': eachStmt(s.body, f, p); if (s.init) eachStmt(s.init, f, p); if (s.update) eachStmt(s.update, f, p); break;
      case 'switch': s.cases.forEach((c) => eachStmt(c, f, p)); break;
      case 'try': eachStmt(s.body, f, p); s.handlers.forEach((h) => eachStmt(h, f, p)); eachStmt(s.fin, f, p); break;
      case 'def': break; // nested functions are analysed on their own
      default: break;
    }
  }
}

/** Visit every expression found anywhere in a statement list. */
export function eachStmtExprs(stmts, f) {
  eachStmt(stmts, (s) => {
    const ex = [];
    switch (s.s) {
      case 'decl': ex.push(s.init); break;
      case 'assign': ex.push(s.target, s.v); break;
      case 'expr': ex.push(s.e); break;
      case 'if': ex.push(s.cond); break;
      case 'while': ex.push(s.cond); break;
      case 'for': ex.push(s.cond, s.iter, s.lo, s.hi, s.step); break;
      case 'return': ex.push(s.v); break;
      case 'switch': ex.push(s.disc); break;
      case 'del': ex.push(s.target); break;
      default: break;
    }
    ex.forEach((e) => eachExpr(e, f));
  });
}

export function eqE(a, b) {
  if (!a || !b) return a === b;
  if (a.t !== b.t) return false;
  switch (a.t) {
    case 'num': return a.v === b.v;
    case 'id': return a.n === b.n;
    case 'op': return a.o === b.o && a.a.length === b.a.length && a.a.every((x, i) => eqE(x, b.a[i]));
    case 'idx': return eqE(a.o, b.o) && eqE(a.i, b.i);
    case 'attr': return a.n === b.n && eqE(a.o, b.o);
    case 'call': return a.fn === b.fn && a.m === b.m && eqE(a.recv, b.recv) && a.a.length === b.a.length && a.a.every((x, i) => eqE(x, b.a[i]));
    case 'lit': case 'tuple': return a.kind === b.kind && a.a.length === b.a.length && a.a.every((x, i) => eqE(x, b.a[i]));
    case 'null': return true;
    default: return false;
  }
}

export function idsIn(e) { const s = new Set(); eachExpr(e, (x) => { if (x.t === 'id') s.add(x.n); }); return s; }
export function mentions(e, name) { let r = false; eachExpr(e, (x) => { if (x.t === 'id' && x.n === name) r = true; }); return r; }

/** short source-like rendering of an expression (for explanations) */
export function show(e, depth = 0) {
  if (!e) return '';
  if (depth > 4) return '…';
  const S = (x) => show(x, depth + 1);
  switch (e.t) {
    case 'num': return e.chr ? "'c'" : e.bool ? (e.v ? 'true' : 'false') : String(e.v);
    case 'id': return e.n;
    case 'null': return 'null';
    case 'op': {
      if (e.o === 'neg') return `-${S(e.a[0])}`;
      if (e.o === '!') return `!${S(e.a[0])}`;
      if (e.o === '?:') return `${S(e.a[0])} ? ${S(e.a[1])} : ${S(e.a[2])}`;
      if (e.o === 'fstr') return 'f"…"';
      return e.a.map(S).join(` ${e.o === 'notin' ? 'not in' : e.o} `);
    }
    case 'idx': return `${S(e.o)}[${S(e.i)}]`;
    case 'slice': return `${S(e.o)}[${e.lo ? S(e.lo) : ''}:${e.hi ? S(e.hi) : ''}]`;
    case 'attr': return `${S(e.o)}.${e.n}`;
    case 'call': return e.recv ? `${S(e.recv)}.${e.m}(${e.a.map(S).join(', ')})` : `${e.fn}(${e.a.map(S).join(', ')})`;
    case 'lit': return e.kind === 'str' ? '"…"' : e.kind === 'list' ? `[${e.a.map(S).join(', ')}]` : e.kind === 'tuple' ? `(${e.a.map(S).join(', ')})` : e.kind === 'set' ? `{${e.a.map(S).join(', ')}}` : '{…}';
    case 'new': return `new ${(e.ty && (e.ty.cls || e.ty.k)) || ''}(${e.a.map(S).join(', ')})`;
    case 'assign': return `${S(e.target)} ${e.op} ${S(e.v)}`;
    case 'incdec': return `${S(e.target)}${e.op}`;
    case 'comp': return `[… for ${e.gens.map((g) => `${g.vars.join(',')} in ${S(g.iter)}`).join(' for ')}]`;
    case 'lambda': return 'lambda';
    case 'tuple': return `(${e.a.map(S).join(', ')})`;
    default: return '…';
  }
}
