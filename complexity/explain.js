// Turns the analyzer's derivation tree into plain, JSON-serialisable bullets and step-by-step calculations.
import * as A from './algebra.js';
import { show } from './util.js';

const strip = (s) => s.replace(/^O\(|\)$/g, '');
const num = (x) => (x >= 1e15 ? x.toExponential(1) : Math.round(x).toLocaleString('en-US'));

export function symbolTable(an) {
  const out = [];
  const seen = new Set();
  for (const [, s] of an.psyms) {
    const id = s[0] && Object.keys(s[0].p)[0] || null;
    if (!id || seen.has(id)) continue; seen.add(id);
    const info = an.syms[id]; if (info) out.push({ id, name: info.name, desc: info.desc });
  }
  return out;
}

function lineTag(n) { return n.line ? `line ${n.line}` : ''; }

/** step-by-step calculation lines: [{depth, line, title, why, formula}] */
function walk(an, node, depth, out, ctx) {
  for (const c of node.children) {
    switch (c.kind) {
      case 'loop': {
        const per = c.body ? strip(an.fmt(c.body)) : '1';
        const trips = c.trips ? strip(an.fmt(c.trips)) : '?';
        const formula = c.amortized
          ? `all runs together: ${trips} × (${per}) = ${an.fmt(c.cost || c.body || A.ONE)}  (counted once, not per outer iteration)`
          : `${trips} iterations × (${per} per iteration) = ${an.fmt(c.cost || A.ONE)}`;
        out.push({ depth, line: c.line, kind: 'loop', title: `\`${c.text}\``, why: c.why || '', formula, count: ctx.lineCount && ctx.lineCount[c.line] });
        walk(an, c, depth + 1, out, ctx);
        break;
      }
      case 'stmt': {
        out.push({ depth, line: c.line, kind: 'stmt', title: c.text, why: 'this statement is not constant-time (library call / copy / allocation)', formula: `costs ${an.fmt(c.cost)}`, count: ctx.lineCount && ctx.lineCount[c.line] });
        break;
      }
      case 'call': {
        out.push({ depth, line: c.line, kind: 'call', title: c.text, why: 'the called function is analysed with the arguments passed here', formula: `costs ${an.fmt(c.cost || A.ONE)}`, count: ctx.lineCount && ctx.lineCount[c.line] });
        walk(an, c, depth + 1, out, ctx);
        break;
      }
      case 'recursion': {
        const p = c.plan || {};
        out.push({ depth, line: c.line, kind: 'recursion', title: c.text, why: p.why || '', formula: `calls: ${p.calls ? an.fmt(p.calls) : 'see recurrence'} × cost of one call ${c.own ? an.fmt(c.own) : ''} → ${an.fmt(c.cost || A.ONE)}`, upper: p.upper });
        walk(an, c, depth + 1, out, ctx);
        break;
      }
      case 'region': {
        out.push({ depth, line: c.line, kind: 'region', title: c.text, why: c.why || '', formula: `executed ≤ ${strip(an.fmt(c.trips))} times in total → ${an.fmt(c.cost || A.ONE)}` });
        walk(an, c, depth + 1, out, ctx);
        break;
      }
      default: walk(an, c, depth, out, ctx);
    }
  }
}

/** short bullet points (what a beginner reads first) */
function timeBullets(an, res, steps, symbols) {
  const b = [];
  const big = an.fmt(res.time);
  const where = symbols.map((s) => `**${s.name}** = ${s.desc}`).join('; ');
  b.push(`Total running time (worst case): **${big}**${where ? ` — where ${where}` : ''}.`);
  const loops = steps.filter((s) => s.kind === 'loop');
  const recs = steps.filter((s) => s.kind === 'recursion');
  const tops = steps.filter((s) => s.depth === 0);
  for (const s of tops) {
    if (s.kind === 'loop') {
      const inner = steps.filter((x) => x.kind === 'loop' && x.depth > s.depth && steps.indexOf(x) > steps.indexOf(s) && (steps.slice(steps.indexOf(s) + 1, steps.indexOf(x)).every((y) => y.depth > s.depth)));
      b.push(`Line ${s.line} ${s.title} — ${s.why}${inner.length ? `; it contains ${inner.length === 1 ? 'another loop' : inner.length + ' more loops'} (line${inner.length === 1 ? '' : 's'} ${inner.map((x) => x.line).join(', ')}), so their iteration counts are **multiplied**.` : '.'}`);
    } else if (s.kind === 'recursion') b.push(`Recursion: ${s.why}.`);
    else if (s.kind === 'stmt') b.push(`Line ${s.line} ${s.title} ${s.formula.replace('costs', 'costs')} (${s.why}).`);
    else if (s.kind === 'call') b.push(`Line ${s.line} ${s.title}: ${s.formula}.`);
  }
  if (loops.length > 1 || tops.length > 1) b.push('Parts that run one after another are **added**; parts nested inside each other are **multiplied**. Only the biggest term matters in Big-O, and constants are dropped.');
  else if (!loops.length && !recs.length) b.push('There are no loops or recursion, so the number of steps does not depend on the input size.');
  return b;
}

function spaceBullets(an, res, space, symbols) {
  const b = [];
  if (space.err) { b.push(`Space cannot be determined reliably: ${space.err.reason}.`); return b; }
  b.push(`Extra memory (beyond the input itself): **${an.fmt(space.total)}**.`);
  for (const p of space.parts || []) b.push(`\`${p.name}\` (line ${p.line}) can hold up to ${strip(an.fmt(p.bound))} elements.`);
  if (space.rec) b.push(`Recursion keeps one stack frame per active call: ${space.depthWhy || ''}${space.frame && !A.isOne(space.frame) ? `; each frame holds ${an.fmt(space.frame)}${space.geometric ? ' (the frames get smaller by half each level, so they add up to the top frame’s size)' : ''}` : '; each frame is O(1)'}.`);
  for (const o of space.outputs || []) b.push(`The returned \`${o.name}\` (line ${o.line}) holds up to ${strip(an.fmt(o.bound))} elements — this is the **output**, so it is not counted as extra space.`);
  if (!(space.parts || []).length && !space.rec) b.push('No container grows with the input; only a fixed number of variables are used.');
  return b;
}

export function buildReport(an, res, ctx = {}) {
  const symbols = symbolTable(an);
  const steps = []; walk(an, an.root.children[0] || an.root, 0, steps, ctx);
  const space = res.space;
  const report = {
    status: 'ok', entry: res.fn.name, symbols,
    time: { big: an.fmt(res.time), bullets: timeBullets(an, res, steps, symbols), steps },
    space: space.err ? { big: null, reason: space.err.reason, line: space.err.line, bullets: spaceBullets(an, res, space, symbols) }
      : { big: an.fmt(space.total), bullets: spaceBullets(an, res, space, symbols), parts: (space.parts || []).map((p) => ({ name: p.name, line: p.line, bound: an.fmt(p.bound) })), outputs: (space.outputs || []).map((o) => ({ name: o.name, line: o.line, bound: an.fmt(o.bound) })) },
    assumptions: [...an.assumptions.keys()],
    upper: !!(steps.some((s) => s.upper)),
    expr: { time: res.time, space: space.err ? null : space.total },
  };
  return report;
}
export const lineTagOf = lineTag;
export { num, show };
