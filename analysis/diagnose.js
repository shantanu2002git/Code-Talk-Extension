// Finds where a program goes wrong using only real evidence from the traces (never guesses a state).
import { show, fmt } from './analyze.js';
import { sameOutput } from '../problem/page.js';

const J = JSON.stringify;

const ERR_HINTS = [
  [/index.*out of range|IndexError|out of bounds|ArrayIndexOutOfBounds|StringIndexOutOfBounds|IndexOutOfBounds|out-of-bounds/i, 'An index went past the end (or before the start) of a list/array/string. Check loop bounds (`<` vs `<=`), `i-1` / `i+1` at the edges, and empty inputs.'],
  [/NullPointer|null pointer|nullptr|NoneType|AttributeError.*None|dereference/i, 'A pointer / reference was null (None) when the code used it. Add a null check before `.next`, `.left`, `.right` or `.val`.'],
  [/KeyError|NoSuchElement|key not found/i, 'A key was read from a map that does not contain it. Check with `in` / `count` / `containsKey` or use `get` with a default.'],
  [/ZeroDivision|divide by zero|division by zero/i, 'A division by zero happened. Guard the divisor.'],
  [/Stack ?overflow|RecursionError|recursion/i, 'The recursion never reached its base case (or the base case is wrong), so calls kept stacking up.'],
  [/Limit|too long|budget|timeout/i, 'The program ran for too long: likely an infinite loop (loop variable never changes toward the exit condition) or an algorithm that is too slow for this input.'],
  [/Unsupported/i, 'This code uses a feature the visualizer cannot run yet. The code itself may be fine on the judge.'],
];

export function errorHint(err) {
  const s = `${err.type} ${err.message}`;
  for (const [re, t] of ERR_HINTS) if (re.test(s)) return t;
  return '';
}

function lastIndexWhere(steps, p) { for (let i = steps.length - 1; i >= 0; i--) if (p(steps[i])) return i; return -1; }

/** distinct consecutive value sequences per variable name: name -> [{step, v}] */
function sequences(steps) {
  const seqs = new Map();
  steps.forEach((s, i) => {
    for (const bag of [s.vars]) for (const [k, v] of Object.entries(bag || {})) {
      if (v && typeof v === 'object' && !Array.isArray(v) && v.$ !== 'chr' && v.$ !== 'dbl' && v.$ !== 'map' && v.$ !== 'set') continue;
      let a = seqs.get(k); if (!a) { a = []; seqs.set(k, a); }
      const j = J(v);
      if (!a.length || a[a.length - 1].j !== j) a.push({ step: i, v, j });
    }
  });
  return seqs;
}

/** Earliest point where a same-named variable takes a different value than in the reference run. */
export function firstDivergence(userSteps, refSteps) {
  const U = sequences(userSteps), R = sequences(refSteps);
  let best = null;
  for (const [name, us] of U) {
    const rs = R.get(name);
    if (!rs || rs.length < 2 || us.length < 2) continue;
    const n = Math.min(us.length, rs.length);
    for (let k = 0; k < n; k++) {
      if (us[k].j !== rs[k].j) {
        // the correct run never shows this value at this stage
        if (!best || us[k].step < best.step) best = { name, step: us[k].step, user: us[k].v, ref: rs[k].v, refStep: rs[k].step, k };
        break;
      }
    }
    if (us.length !== rs.length && !best) {
      // one run kept changing the variable and the other stopped
      const k = n; const longer = us.length > rs.length ? us : rs;
      const st = us.length > rs.length ? us[k].step : userSteps.length - 1;
      if (!best || st < best.step) best = { name, step: st, user: us.length > rs.length ? us[k].v : us[us.length - 1].v, ref: us.length > rs.length ? rs[rs.length - 1].v : rs[k].v, refStep: 0, k, extra: longer === us ? 'user-more' : 'ref-more' };
    }
  }
  return best;
}

function features(code, steps) {
  const c = String(code);
  const nest = (() => { let max = 0; const stack = []; for (const L of c.split('\n')) { const ind = L.match(/^[\t ]*/)[0].replace(/\t/g, '    ').length; while (stack.length && stack[stack.length - 1] >= ind) stack.pop(); if (/^\s*(for|while)\b/.test(L)) { stack.push(ind); max = Math.max(max, stack.length); } } return max; })();
  const uses = [];
  if (/unordered_map|HashMap|Map<|\bdict\b|\{\}|defaultdict|Counter|map</.test(c)) uses.push('hash map');
  if (/unordered_set|HashSet|Set<|\bset\(|set</.test(c)) uses.push('set');
  if (/stack|Stack/.test(c)) uses.push('stack');
  if (/queue|Queue|deque|Deque/.test(c)) uses.push('queue');
  if (/priority_queue|PriorityQueue|heapq/.test(c)) uses.push('heap');
  if (/\bsort\b|sorted\(|Arrays\.sort|Collections\.sort/.test(c)) uses.push('sorting');
  const depth = steps.reduce((m, s) => Math.max(m, s.depth || 1), 1);
  return { loopNest: nest, uses, steps: steps.length, depth };
}

/**
 * run: result of the user's run {ok, error, result, steps, warnings, argsAfter, stdout}
 * expected: expected output (or undefined)
 * ref: optional {run, code} reference trace on the same input
 */
export function diagnose({ run, code, lang, expected, ref, entrySig, lines }) {
  const out = { verdict: 'unknown', findings: [], jumpTo: null, compare: null };
  const add = (f) => out.findings.push(f);
  const steps = run.steps || [];
  let got = run.result;
  if (got === undefined && run.argsAfter && entrySig && entrySig.ret === 'void') got = run.argsAfter[0];

  if (run.error) {
    const e = run.error;
    const idx = lastIndexWhere(steps, (s) => s.ev === 'error');
    const lineNo = e.line || (idx >= 0 ? steps[idx].line : null);
    const lt = lineNo && lines ? (lines[lineNo - 1] || '').trim() : '';
    if (e.kind === 'syntax') { out.verdict = 'syntax'; add({ sev: 'bad', title: 'Syntax problem', text: `${e.message}${lineNo ? ` (line ${lineNo})` : ''}. The code does not compile/parse, so it cannot be traced.`, line: lineNo }); }
    else if (e.kind === 'unsupported') { out.verdict = 'unsupported'; add({ sev: 'warn', title: 'Not supported by the visualizer', text: e.message, line: lineNo }); }
    else {
      out.verdict = 'error';
      add({ sev: 'bad', title: e.kind === 'limit' ? 'Stopped: too long / infinite loop?' : `Crash: ${e.type}`, text: `${e.message}${lineNo ? ` — on line ${lineNo}${lt ? `: \`${lt}\`` : ''}` : ''}.`, line: lineNo, step: idx >= 0 ? idx : null });
      const hint = errorHint(e);
      if (hint) add({ sev: 'info', title: 'Why this usually happens', text: hint });
      if (idx >= 0) {
        const s = steps[idx];
        const vs = Object.entries(s.vars || {}).slice(0, 6).map(([k, v]) => `${k} = ${show(v, 28)}`).join(', ');
        if (vs) add({ sev: 'info', title: 'State at the moment of failure', text: vs, step: idx });
        out.jumpTo = idx;
      }
    }
  } else {
    if (expected !== undefined && got !== undefined) {
      const cmp = sameOutput(got, expected);
      if (cmp === 'exact') { out.verdict = 'correct'; add({ sev: 'good', title: 'Output matches the expected answer', text: `Got ${show(got, 80)}.` }); }
      else if (cmp === 'reordered') { out.verdict = 'reordered'; add({ sev: 'warn', title: 'Same items, different order', text: `Got ${show(got, 80)}, expected ${show(expected, 80)}. Many problems accept any order; check the statement.` }); }
      else {
        out.verdict = 'wrong'; add({ sev: 'bad', title: 'Wrong answer on this input', text: `Got ${show(got, 80)} but the expected answer is ${show(expected, 80)}.` });
        const ri = lastIndexWhere(steps, (s) => s.ev === 'return' && s.depth === 1);
        if (ri >= 0) {
          const rs = steps[ri];
          const vs = Object.entries(rs.vars || {}).filter(([, v]) => v === null || typeof v !== 'object' || ['chr', 'dbl'].includes(v.$)).slice(0, 6).map(([k, v]) => `${k} = ${show(v, 20)}`).join(', ');
          add({ sev: 'bad', title: 'Where the wrong answer was produced', text: `The function returned ${show(rs.ret, 60)} at line ${rs.line}${lines && lines[rs.line - 1] ? ` (\`${lines[rs.line - 1].trim()}\`)` : ''}${vs ? ` when ${vs}` : ''}. Step through to see how the code reached this point.`, step: ri, line: rs.line });
          out.jumpTo = ri;
        }
      }
    } else if (got !== undefined) { out.verdict = 'ran'; add({ sev: 'info', title: 'Program finished', text: `Returned ${show(got, 80)}. No expected output was available to compare.` }); }
    if (run.truncated) add({ sev: 'info', title: 'Long run', text: 'Only the first part of the execution is shown (the player is capped), but the program was run to the end.' });
  }

  for (const w of run.warnings || []) add({ sev: 'warn', title: 'Suspicious access', text: String(w).slice(0, 200) });

  // evidence from the trace itself
  if (!run.error && steps.length) {
    const lineHit = new Set(steps.map((s) => s.line));
    // loop that never advanced: same line + same vars many times
    // returned value equals the initial value of a result variable
    const ret = steps.find((s) => s.ev === 'return' && s.depth === 1);
    if ((out.verdict === 'wrong') && ret) {
      const first = steps[0];
      for (const [k, v] of Object.entries(first.vars || {})) {
        if (/^(ans|res|result|count|cnt|ret|answer|best|total)$/i.test(k) && J(v) === J(ret.ret)) add({ sev: 'warn', title: 'Result never changed', text: `\`${k}\` was returned with its initial value ${show(v, 30)}: the code path that should update it never ran.` });
      }
    }
    if (out.verdict === 'wrong' || out.verdict === 'reordered') {
      const dead = [];
      if (lines) lines.forEach((L, k) => { const t = L.trim(); if (/^(if|else if|elif|else|for|while)\b/.test(t) || /^return\b/.test(t)) { const hasBody = true; if (hasBody && !lineHit.has(k + 1) && t) dead.push(k + 1); } });
      if (dead.length && dead.length <= 6) add({ sev: 'info', title: 'Lines that never ran on this input', text: `Line${dead.length > 1 ? 's' : ''} ${dead.join(', ')} ${dead.length > 1 ? 'were' : 'was'} never executed. If one of them handles a case that this input needs, that is a good place to look.`, line: dead[0] });
    }
  }

  // comparison with the reference run
  if (ref && ref.run && !ref.run.error) {
    const div = (out.verdict === 'wrong' || out.verdict === 'error' || out.verdict === 'reordered') ? firstDivergence(steps, ref.run.steps || []) : null;
    const uf = features(code, steps), rf = features(ref.code, ref.run.steps || []);
    out.compare = { user: uf, ref: rf };
    if (div) {
      const s = steps[div.step];
      add({ sev: 'bad', title: 'First visible difference from the correct solution', text: `\`${div.name}\` becomes ${show(div.user, 50)} here, while the correct solution's \`${div.name}\` is ${show(div.ref, 50)} at the same stage (line ${s ? s.line : '?'}). This is inferred by lining up same-named variables in both runs.`, step: div.step, line: s ? s.line : null });
      out.jumpTo = out.jumpTo === null ? div.step : out.jumpTo;
    } else if (out.verdict === 'wrong' || out.verdict === 'error') add({ sev: 'info', title: 'Different approach', text: 'No same-named variable lines up with the correct solution, so the difference is in the approach rather than one value. See the comparison table.' });
    if (out.verdict !== 'correct' && J(ref.run.result) !== J(got) && ref.run.result !== undefined) add({ sev: 'info', title: 'Correct solution returns', text: show(ref.run.result, 80) });
    if (uf.steps > rf.steps * 4 && rf.steps > 5) add({ sev: 'warn', title: 'Much more work than the correct solution', text: `Your code took ${uf.steps} steps on this tiny input, the correct solution ${rf.steps}. On large inputs this gap grows and may cause Time Limit Exceeded.` });
  }
  return out;
}
