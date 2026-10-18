// "Time & Space complexity" card: static analysis of the code in the editor, a cross-check against measured runs, and a
// plain-language, step-by-step derivation. It recomputes whenever the code, language or mode changes.
import { h } from './dom.js';
import { analyzeComplexity } from '../complexity/index.js';
import { measure, symValues } from '../complexity/measure.js';
import * as A from '../complexity/algebra.js';
import { runTrace, pythonIR } from '../engine/index.js';

/** **bold** and `code` -> nodes */
function rich(text) {
  const out = [];
  String(text).split(/(\*\*[^*]+\*\*|`[^`]+`)/).forEach((p) => {
    if (!p) return;
    if (p.startsWith('**')) out.push(h('b', null, p.slice(2, -2)));
    else if (p.startsWith('`')) out.push(h('code', null, p.slice(1, -1)));
    else out.push(p);
  });
  return out;
}
const fmtN = (x) => (x >= 1e12 ? x.toExponential(1) : Math.round(x).toLocaleString('en-US'));

export function createComplexityPanel({ root, getSource, getRunInfo, onJump }) {
  let token = 0, timer = null, last = null;

  function schedule(delay = 600) { clearTimeout(timer); timer = setTimeout(compute, delay); render({ state: 'busy' }); }

  async function compute() {
    const my = ++token;
    const src = getSource();
    if (!src) { render({ state: 'none', text: 'No code to analyse yet (for “correct solution” mode a bundled or pasted reference is needed).' }); return; }
    if (src.lang === 'javascript') { render({ state: 'none', text: 'JavaScript is not analysable yet — choose C++, Java or Python.' }); return; }
    if (!src.code.trim()) { render({ state: 'none', text: 'Paste or load some code to see its complexity.' }); return; }
    render({ state: 'busy' });
    const info = getRunInfo(src);
    let ir = null;
    if (src.lang === 'python') {
      ir = await pythonIR(src.code);
      if (my !== token) return;
    }
    const entry = info.entry || (ir && ir.funcs && ir.funcs.length ? ir.funcs[0].name : undefined);
    if (!entry) { render({ state: 'und', reason: 'no function to analyse was found in the code', src }); return; }
    const lineCount = info.lineCount || null;
    const r = analyzeComplexity({ lang: src.lang, code: src.code, entry, ir, ctx: { lineCount } });
    if (my !== token) return;
    if (!r.ok) { last = { src, r }; render({ state: 'und', reason: r.reason, line: r.line, assumptions: r.assumptions, src, internal: r.internal }); return; }
    // concrete numbers for the example input
    let example = null;
    if (info.args) {
      try { const vals = symValues(r.analyzer, r.result.fn, info.args); example = { vals, time: A.evalE(r.result.time, vals), space: r.result.space.err ? null : A.evalE(r.result.space.total, vals), names: Object.fromEntries(Object.keys(vals).map((id) => [id, r.analyzer.symName(id)])) }; } catch { example = null; }
    }
    last = { src, r, example, measure: null };
    render({ state: 'ok', r, example, src, measuring: true, lineCount, truncated: info.truncated });
    // cross-check on generated inputs (can only refute the claim)
    let m = null;
    try {
      const runOps = async (args) => {
        const out = await runTrace({ lang: src.lang, code: src.code, args, entry, maxSteps: 1, maxOps: 2_000_000, maxEvents: 1_500_000 });
        if (!out || out.error) return { ok: false, error: out && out.error ? out.error.message : 'no result' };
        const ops = out.ops !== undefined ? out.ops : out.events;
        return ops === undefined ? { ok: false, error: 'no operation count' } : { ok: true, ops };
      };
      m = await measure(r.analyzer, r.result, (a) => (my === token ? runOps(a) : Promise.resolve({ ok: false })));
    } catch { m = { status: 'unavailable', reason: 'the measurement could not run' }; }
    if (my !== token) return;
    last.measure = m;
    if (m.status === 'contradiction') { render({ state: 'und', reason: 'a measurement contradicted the static result, so no bound is claimed. The static analysis said ' + r.report.time.big + ', but the operation count on generated inputs grew faster than that.', src, contradicted: m }); return; }
    render({ state: 'ok', r, example, src, measure: m, lineCount, truncated: info.truncated });
  }

  function render(st) {
    root.textContent = '';
    root.hidden = false;
    const head = h('div', { class: 'chead' }, 'Time & space complexity', h('span', { class: 'note' }, 'worst case, from your current code'));
    root.append(head);
    if (st.state === 'busy') { root.append(h('div', { class: 'cxmsg' }, '⏳ Analysing the code…')); return; }
    if (st.state === 'none') { root.append(h('div', { class: 'cxmsg' }, st.text)); return; }
    if (st.state === 'und') {
      root.append(
        h('div', { class: 'cxpair' }, badge('Time', null), badge('Space', null)),
        h('div', { class: 'cxund' }, h('b', null, 'Cannot be determined reliably.'), h('p', null, rich(st.reason + (st.line ? ` (line ${st.line})` : ''))),
          h('p', { class: 'note' }, 'Code Talk only reports a complexity when it can prove it from the code. Rather than guess, it stops here. If you simplify this part (for example use a plain counting loop or a standard library call), the analysis can usually continue.'),
          st.internal ? h('p', { class: 'note' }, 'This was an internal limitation of the analyzer, not a property of your code.') : null),
        ...(st.assumptions && st.assumptions.length ? [h('details', null, h('summary', null, 'Assumptions made so far'), h('ul', null, st.assumptions.map((a) => h('li', null, rich(a)))))] : []));
      return;
    }
    const { r, example, measure: m } = st;
    const rep = r.report;
    root.append(h('div', { class: 'cxpair' }, badge('Time', rep.time.big, example && example.time !== undefined ? `≈ ${fmtN(example.time)} steps for your example` : ''), badge('Space', rep.space.big, example && example.space ? `≈ ${fmtN(example.space)} items for your example` : '', rep.space.reason)));
    const names = rep.symbols;
    if (names.length) root.append(h('div', { class: 'cxsyms' }, 'Where ', names.map((s, i) => [i ? ' · ' : '', h('code', null, s.name), ' = ', s.desc.replace(/`/g, '')]), example ? h('span', { class: 'note' }, `  (your example: ${Object.entries(example.vals).map(([id, v]) => `${example.names[id]} = ${fmtN(v)}`).join(', ')})`) : null));
    if (rep.upper) root.append(h('div', { class: 'cxwarn' }, 'This is an upper bound: the real running time can be smaller, but never larger.'));

    root.append(h('h4', null, 'Time — in simple words'), h('ul', { class: 'cxlist' }, rep.time.bullets.map((b) => h('li', null, rich(b)))));
    root.append(h('h4', null, 'Space — in simple words'), h('ul', { class: 'cxlist' }, rep.space.bullets.map((b) => h('li', null, rich(b)))));
    if (rep.space.reason) root.append(h('div', { class: 'cxund' }, h('b', null, 'Space cannot be determined reliably.'), h('p', null, rich(rep.space.reason + (rep.space.line ? ` (line ${rep.space.line})` : '')))));

    // step-by-step calculation
    const steps = rep.time.steps;
    const det = h('details', { class: 'cxsteps', open: steps.length > 0 && steps.length <= 6 }, h('summary', null, `Step-by-step: how ${rep.time.big} is calculated`));
    if (!steps.length) det.append(h('p', null, 'There are no loops, recursion or non-trivial library calls: every statement takes a fixed amount of time, so the total is O(1).'));
    for (const s of steps) {
      const cnt = st.lineCount && st.lineCount[s.line];
      det.append(h('div', { class: 'cxstep', style: { marginLeft: `${Math.min(s.depth, 5) * 12}px` } },
        h('div', { class: 'cxs1' }, h('button', { class: 'ln-btn', title: 'Show this line in the code', onclick: () => onJump && onJump(s.line) }, `line ${s.line || '?'}`), ' ', rich(s.title)),
        s.why ? h('div', { class: 'cxs2' }, rich(s.why)) : null,
        h('div', { class: 'cxs3' }, rich(s.formula)),
        cnt ? h('div', { class: 'note' }, `In your example run this line was reached ${cnt.toLocaleString('en-US')} time${cnt === 1 ? '' : 's'}${st.truncated ? ' (the recorded part of the run)' : ''}.`) : null));
    }
    det.append(h('p', { class: 'note' }, 'Rules: loops nested inside each other multiply, statements one after another add, and only the fastest-growing term is kept (constants and smaller terms are dropped).'));
    root.append(det);

    if (rep.space.parts && rep.space.parts.length) root.append(h('details', null, h('summary', null, 'Where the memory goes'), h('ul', { class: 'cxlist' }, rep.space.parts.map((p) => h('li', null, h('code', null, p.name), ` (line ${p.line}): ${p.bound}`)))));
    if (rep.assumptions.length) root.append(h('details', null, h('summary', null, `Assumptions (${rep.assumptions.length})`), h('ul', { class: 'cxlist' }, rep.assumptions.map((a) => h('li', null, rich(a))))));

    // evidence
    if (st.measuring) root.append(h('div', { class: 'cxev note' }, '⏳ Cross-checking against real runs on generated inputs…'));
    else if (m) {
      const pts = m.points || [];
      if (m.status === 'consistent') root.append(h('div', { class: 'cxev good' }, `✓ Cross-check: your code was run on generated inputs of growing size (${pts.map((p) => p.N).join(', ')}); the number of operations (${pts.map((p) => fmtN(p.ops)).join(' → ')}) grows in line with ${rep.time.big}.`));
      else if (m.status === 'looser') root.append(h('div', { class: 'cxev warn' }, `Cross-check: on generated inputs the operation counts (${pts.map((p) => fmtN(p.ops)).join(' → ')}) grew more slowly than ${rep.time.big}. The bound is still a valid worst case, but typical inputs may exit early, or a library call may hide a log factor — so it may not be tight.`));
      else root.append(h('div', { class: 'cxev note' }, `Cross-check unavailable: ${m.reason || 'no measurement'}.`));
    }
  }

  function badge(label, value, sub = '', reason = '') {
    return h('div', { class: `cxbadge ${value ? '' : 'none'}` }, h('div', { class: 'cxl' }, label), h('div', { class: 'cxv' }, value || 'not determined'), sub ? h('div', { class: 'cxsub' }, sub) : null, reason && !value ? h('div', { class: 'cxsub' }, 'see below') : null);
  }

  return { schedule, compute, get last() { return last; } };
}
