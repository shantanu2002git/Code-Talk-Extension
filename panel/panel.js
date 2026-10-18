// Code Talk side panel controller.
import { h } from './dom.js';
import { runTrace, warmupPython } from '../engine/index.js';
import { detectEntries } from '../engine/clike/run.js';
import { analyze, show } from '../analysis/analyze.js';
import { diagnose } from '../analysis/diagnose.js';
import { examplesFromText, parseInputText, mapArgs, normLang, guessLang, outputOf } from '../problem/page.js';
import { findProblem, pickReference } from '../reference/lookup.js';
import { createComplexityPanel } from './complexity.js';
import { renderCode, renderExplain, renderVars, renderHints, renderCalls, renderStack } from './view.js';

const $ = (id) => document.getElementById(id);
const LANG_NAMES = { cpp: 'C++', java: 'Java', python: 'Python', javascript: 'JavaScript' };

const S = {
  page: null, mode: 'mine', examples: [], exIndex: 0, expected: undefined, expectedKnown: false,
  library: null, trace: null, an: null, lines: [], code: '', lang: 'cpp', step: 0, playing: false, timer: null, tabId: null, tabUrl: '', running: false, userEdited: false, diag: null,
};

// ---------------------------------------------------------------- status
function status(text, kind = '') { const el = $('status'); el.textContent = text || ''; el.className = `status ${kind}`; }

// ---------------------------------------------------------------- page access
async function activeTab() {
  const q = new URLSearchParams(location.search).get('tab');
  if (q) return chrome.tabs.get(Number(q));
  const [t] = await chrome.tabs.query({ active: true, lastFocusedWindow: true });
  return t || null;
}
async function readPage(tab) {
  if (!tab || !tab.id) return null;
  try {
    await chrome.scripting.executeScript({ target: { tabId: tab.id }, world: 'MAIN', files: ['content/extract.js'] });
    const [res] = await chrome.scripting.executeScript({ target: { tabId: tab.id }, world: 'MAIN', func: () => (window.__codeTalkExtract ? window.__codeTalkExtract() : null) });
    return res && res.result ? res.result : null;
  } catch (e) {
    return { ok: false, error: /Cannot access|permission|host/i.test(String(e.message)) ? 'Code Talk is not allowed on this page. Open a LeetCode or GeeksforGeeks problem, or paste code manually.' : String(e.message) };
  }
}

// ---------------------------------------------------------------- problem loading
function setProblem(p) {
  S.page = p;
  const ok = p && p.ok !== false;
  $('siteBadge').textContent = ok ? (p.site === 'leetcode' ? 'LeetCode' : p.site === 'gfg' ? 'GeeksforGeeks' : 'manual mode') : 'manual mode';
  $('pTitle').textContent = ok && p.title ? `${p.number ? p.number + '. ' : ''}${p.title}` : 'No problem detected';
  $('pMeta').textContent = ok ? [p.slug && `slug: ${p.slug}`, p.editor && `editor: ${p.editor}`, p.languageLabel && `language: ${p.languageLabel}`].filter(Boolean).join(' · ') || 'Paste your code below to visualize it.' : (p && p.error) || 'Open a problem on leetcode.com or geeksforgeeks.org, or paste code below.';
  $('pDesc').textContent = ok ? p.description || '(statement not found on the page)' : '';
}

async function applyPage(p, { keepCode = false } = {}) {
  setProblem(p);
  const ok = p && p.ok !== false;
  const notes = (p && p.notes) || [];
  $('codeNote').textContent = notes.join(' ');
  if (ok && p.code && !keepCode) {
    $('codeBox').value = p.code;
    const lang = normLang(p.language || p.languageLabel, p.code);
    $('langSel').value = LANG_NAMES[lang] && [...$('langSel').options].some((o) => o.value === lang) ? lang : 'cpp';
    if (lang === 'javascript') { $('langSel').value = 'javascript'; }
  }
  S.userEdited = false;
  // examples: from the page statement, otherwise from the bundled library
  let exs = ok ? examplesFromText(p.description, p.site).filter((e) => e.inputs && e.expected !== undefined) : [];
  S.library = ok ? await findProblem({ slug: p.slug, title: p.title }) : null;
  if (!exs.length && S.library) exs = S.library.examples.map((e) => ({ inputs: e.input, expected: e.expected, inputText: e.input.map((i) => `${i.name} = ${JSON.stringify(i.value)}`).join(', '), fromLibrary: true }));
  S.examples = exs;
  const sel = $('exSel'); sel.textContent = '';
  exs.forEach((e, i) => sel.append(h('option', { value: i }, `Example ${i + 1}: ${e.inputText.slice(0, 48)}${e.inputText.length > 48 ? '…' : ''}`)));
  sel.append(h('option', { value: -1 }, exs.length ? 'Custom input…' : 'Custom input'));
  sel.value = exs.length ? '0' : '-1';
  pickExample();
  S.trace = null; $('results').hidden = true; stopPlay();
}

function pickExample() {
  const i = Number($('exSel').value);
  const e = S.examples[i];
  if (e) {
    $('inputBox').value = e.inputs.map((x) => `${x.name} = ${typeof x.value === 'string' && x.raw === undefined ? JSON.stringify(x.value) : (x.raw !== undefined ? x.raw : JSON.stringify(x.value))}`).join(', ');
    S.expected = e.expected; S.expectedKnown = true;
  } else { S.expected = undefined; S.expectedKnown = false; }
}

// ---------------------------------------------------------------- entry parameter names (to map example inputs onto them)
function paramsFor(lang, code, argc) {
  try {
    if (lang === 'cpp' || lang === 'java') {
      const d = detectEntries(lang, code);
      const fit = d.candidates.filter((c) => c.params.length === argc);
      const c = fit[0] || d.candidates[0];
      return c ? { entry: c.name, params: c.params } : { entry: undefined, params: null };
    }
    if (lang === 'python') {
      const defs = [];
      const re = /^([ \t]*)def\s+(\w+)\s*\(([^)]*)\)/gm; let m;
      while ((m = re.exec(code))) {
        if (m[2].startsWith('__')) continue;
        const ps = m[3].split(',').map((x) => x.trim().split(':')[0].split('=')[0].trim()).filter((x) => x && x !== 'self' && x !== 'cls');
        defs.push({ name: m[2], indent: m[1].replace(/\t/g, '    ').length, params: ps.map((n) => ({ name: n })) });
      }
      const min = Math.min(...defs.map((d) => d.indent), 0);
      const top = defs.filter((d) => d.indent === min || (/class\s+Solution/.test(code) && d.indent > 0 && d.indent <= 8));
      const called = (n) => new RegExp(`(?:self\\.|\\b)${n}\\s*\\(`, 'g');
      const scored = top.map((d) => ({ d, calls: (code.match(called(d.name)) || []).length - 1, fit: d.params.length === argc ? 1 : 0 }));
      scored.sort((a, b) => b.fit - a.fit || a.calls - b.calls);
      const c = scored[0] && scored[0].d;
      return c ? { entry: c.name, params: c.params } : { entry: undefined, params: null };
    }
  } catch { /* fall through */ }
  return { entry: undefined, params: null };
}

// ---------------------------------------------------------------- complexity card
let cx = null;
function cxSource() {
  const lang = $('langSel').value;
  if (S.mode === 'correct') {
    const pasted = $('refBox').value.trim();
    const r = pasted ? { lang, code: pasted } : (S.library ? pickReference(S.library, lang) : null);
    return r ? { lang: r.lang, code: r.code } : null;
  }
  return { lang, code: $('codeBox').value };
}
function cxRunInfo(src) {
  let args = null, argc = 0;
  try { const parsed = parseInputText($('inputBox').value); if (!parsed.error) argc = parsed.inputs.length; } catch {}
  const probe = paramsFor(src.lang, src.code, argc);
  try { const parsed = parseInputText($('inputBox').value); if (!parsed.error) { const m = mapArgs(parsed.inputs, probe.params); if (m.args) args = JSON.parse(JSON.stringify(m.args)); } } catch {}
  let lineCount = null, truncated = false;
  if (S.trace && S.code === src.code && S.lang === src.lang) {
    lineCount = {}; for (const st of S.trace.steps) if (st.ev === 'line') lineCount[st.line] = (lineCount[st.line] || 0) + 1;
    truncated = Boolean(S.trace.truncated);
  }
  return { entry: probe.entry, args, lineCount, truncated };
}
function cxJump(line) { const el = document.querySelector(`#codeView .ln[data-n="${line}"]`); if (el && el.scrollIntoView) el.scrollIntoView({ block: 'center' }); }

// ---------------------------------------------------------------- running
async function execute(code, lang, inputs) {
  const probe = paramsFor(lang, code, inputs.length);
  const mapped = mapArgs(inputs, probe.params);
  if (!mapped.args) return { run: null, error: mapped.note, probe };
  const run = await runTrace({ lang, code, args: JSON.parse(JSON.stringify(mapped.args)), entry: probe.entry, maxSteps: 3000, onStatus: (t) => status(t, 'busy') });
  return { run, args: mapped.args, note: mapped.note, probe };
}

async function runAll() {
  if (S.running) { S.pending = true; return; }
  S.running = true; $('btnRun').disabled = true; stopPlay();
  const mode = S.mode; // the mode can be switched while a run is in flight
  try {
    const lang0 = $('langSel').value;
    const parsed = parseInputText($('inputBox').value);
    if (parsed.error) { status(parsed.error, 'err'); return; }
    let code, lang = lang0, refInfo = null, refEntry = null;
    if (mode === 'correct') {
      const pasted = $('refBox').value.trim();
      if (pasted) refInfo = { lang: lang0, code: pasted, exact: true, pasted: true };
      else { refEntry = S.library; refInfo = pickReference(refEntry, lang0); }
      if (!refInfo) { status('No bundled correct solution for this problem yet. Paste a known-good solution into the box that appeared below the code, then press Visualize again.', 'err'); $('refBlock').hidden = false; return; }
      code = refInfo.code; lang = refInfo.lang;
    } else {
      code = $('codeBox').value;
      if (!code.trim()) { status('Paste or load some code first.', 'err'); return; }
    }
    if (lang === 'javascript') { status('JavaScript cannot be traced yet. Choose C++, Java or Python (paste the code in that language).', 'err'); return; }
    status(lang === 'python' ? 'Running Python (the first run loads the runtime — a few seconds)…' : 'Running…', 'busy');
    const { run, error, args, note } = await execute(code, lang, parsed.inputs);
    if (!run) { status(error, 'err'); return; }
    S.runMode = mode; S.code = code; S.lang = lang; S.lines = code.replace(/\r/g, '').split('\n');
    S.trace = run; S.trace.steps = run.steps || [];
    S.an = analyze({ steps: S.trace.steps, code, lang });
    const expected = S.expectedKnown ? S.expected : undefined;
    const got = outputOf(run, args);
    run.result = got === undefined && run.result === null ? null : run.result;
    // comparison with the bundled correct solution (same language, mine-mode, only when it can help)
    let ref = null;
    if (mode === 'mine' && S.library) {
      const r = pickReference(S.library, lang);
      if (r && r.exact) {
        status('Comparing with the correct solution…', 'busy');
        const rr = await execute(r.code, lang, parsed.inputs);
        if (rr.run) ref = { run: rr.run, code: r.code, args: rr.args };
      }
    }
    const runForDiag = { ...run, result: got };
    S.diag = diagnose({ run: runForDiag, code, lang, expected, ref, entrySig: run.entrySig, lines: S.lines });
    if (mode === 'correct') S.diag.findings.unshift({ sev: 'info', title: `Correct solution (${LANG_NAMES[lang]})`, text: `${refInfo.pasted ? 'Your pasted reference solution' : `The bundled reference solution for "${S.library ? S.library.title : 'this problem'}"`}${refInfo.exact ? '' : `. No ${LANG_NAMES[lang0]} version is bundled, so the ${LANG_NAMES[lang]} one is shown — the algorithm is the same`}.` });
    if (note) S.diag.findings.push({ sev: 'info', title: 'Input mapping', text: note });
    S.step = 0;
    status('');
    renderAll(true);
    cx.schedule(50);
    if (S.diag.jumpTo !== null && mode === 'mine' && S.diag.verdict !== 'correct') goTo(S.diag.jumpTo);
  } catch (e) {
    status(`Unexpected error: ${e && e.message}`, 'err');
    console.error(e);
  } finally { S.running = false; S.doneCount = (S.doneCount || 0) + 1; $('btnRun').disabled = false; S.runMode = mode; if (S.pending) { S.pending = false; runAll(); } }
}

// ---------------------------------------------------------------- rendering
function renderVerdict() {
  const d = S.diag; const el = $('verdict');
  el.textContent = '';
  const cls = d.verdict === 'correct' ? 'good' : ['wrong', 'error', 'syntax'].includes(d.verdict) ? 'bad' : ['reordered', 'unsupported'].includes(d.verdict) ? 'warn' : '';
  el.className = `card verdict ${cls}`;
  const head = { correct: '✅ Correct on this input', wrong: '❌ Wrong answer', error: '💥 Runtime problem', syntax: '⚠ Syntax problem', unsupported: '⚠ Unsupported code', reordered: '≈ Same items, different order', ran: 'Finished', unknown: 'Result' }[d.verdict] || 'Result';
  el.append(h('div', { class: 't' }, S.runMode === 'correct' ? `Correct solution — ${head}` : head));
  for (const f of d.findings) {
    el.append(h('div', { class: `finding ${f.sev}` }, h('b', null, f.title), h('span', null, f.text),
      f.step !== undefined && f.step !== null ? h('button', { class: 'go', onclick: () => goTo(f.step) }, `Jump to step ${f.step + 1}`) : null));
  }
  const cmp = d.compare;
  $('cmpCard').hidden = !cmp;
  if (cmp) {
    const rows = [['Steps executed', cmp.user.steps, cmp.ref.steps], ['Deepest recursion', cmp.user.depth, cmp.ref.depth], ['Loop nesting (code)', cmp.user.loopNest, cmp.ref.loopNest], ['Data structures (code)', cmp.user.uses.join(', ') || '—', cmp.ref.uses.join(', ') || '—']];
    const t = h('table', { class: 'cmp' }, h('tr', null, h('th'), h('th', null, 'Your code'), h('th', null, 'Correct solution')), rows.map(([a, b, c]) => h('tr', null, h('td', null, a), h('td', null, String(b)), h('td', null, String(c)))));
    $('cmp').textContent = ''; $('cmp').append(t, h('button', { style: { marginTop: '8px' }, onclick: () => setMode('correct', true) }, 'Show the correct solution step by step'));
  }
}

function renderAll(fresh) {
  const tr = S.trace;
  $('results').hidden = false;
  if (fresh) renderVerdict();
  const n = tr.steps.length;
  $('slider').max = String(Math.max(n - 1, 0)); $('slider').disabled = !n;
  for (const id of ['bReset', 'bPrev', 'bPlay', 'bNext']) $(id).disabled = !n;
  document.querySelectorAll('.codecard,.explain,#hintCards,#vars,#callCard,#stackCard').forEach((e) => { if (e.closest) e.hidden = !n && e.id !== 'callCard'; });
  $('callCard').hidden = !n;
  $('codeTitle').textContent = S.runMode === 'correct' ? `Correct solution · ${LANG_NAMES[S.lang]}` : `Your code · ${LANG_NAMES[S.lang]}`;
  $('codeSub').textContent = n ? `${n} steps${tr.truncated ? ' (first part of a longer run)' : ''}` : '';
  S.codeKey = `${S.runMode}|${S.lang}|${S.code.length}|${S.code.slice(0, 40)}|${Date.now()}`;
  $('codeView').dataset.key = '';
  if (!n) { renderCode($('codeView'), { ...S, step: 0, trace: { steps: [] }, errorLine: S.diag.findings.find((f) => f.line)?.line }); $('stepNo').textContent = 'No steps recorded'; return; }
  renderStep();
}

function renderStep() {
  const tr = S.trace; const n = tr.steps.length;
  if (!n) return;
  S.step = Math.max(0, Math.min(n - 1, S.step));
  const errLine = tr.error ? (S.diag.findings.find((f) => f.line) || {}).line : null;
  const st = { ...S, errorLine: errLine };
  renderCode($('codeView'), st);
  renderExplain($('explainCard'), st);
  renderHints($('hintCards'), st);
  renderVars($('vars'), $('varNote'), st);
  renderCalls($('callCard'), $('callTree'), st, (i) => goTo(i));
  renderStack($('callStack'), st);
  const s = tr.steps[S.step];
  $('slider').value = String(S.step);
  $('stepNo').textContent = `Step ${S.step + 1} / ${n}`;
  $('frameInfo').textContent = `${s.fn || ''}${s.depth > 1 ? ` · depth ${s.depth}` : ''}`;
  const out = s.out !== undefined ? s.out : (S.step === n - 1 ? tr.stdout : '');
  $('outCard').hidden = !out; $('stdout').textContent = out || '';
  $('bPlay').textContent = S.playing ? '⏸' : '▶';
}

// ---------------------------------------------------------------- player
function goTo(i) { S.step = i; renderStep(); $('codeView').closest('.card').scrollIntoView?.({ block: 'nearest' }); }
function stopPlay() { S.playing = false; clearTimeout(S.timer); const b = $('bPlay'); if (b) b.textContent = '▶'; }
function tick() {
  if (!S.playing || !S.trace) return;
  if (S.step >= S.trace.steps.length - 1) { stopPlay(); return; }
  S.step++; renderStep();
  S.timer = setTimeout(tick, 900 / Number($('speedSel').value));
}
function togglePlay() {
  if (!S.trace || !S.trace.steps.length) return;
  if (S.playing) { stopPlay(); return; }
  if (S.step >= S.trace.steps.length - 1) S.step = 0;
  S.playing = true; $('bPlay').textContent = '⏸'; tick();
}

// ---------------------------------------------------------------- mode
function setMode(mode, run) {
  S.mode = mode;
  document.querySelectorAll('#modeSeg button').forEach((b) => b.classList.toggle('on', b.dataset.mode === mode));
  $('refBlock').hidden = mode !== 'correct' || !$('refBox').value.trim();
  if (cx) cx.schedule(100);
  if (run) runAll();
}

// ---------------------------------------------------------------- wiring
async function refresh({ auto = true, keepCode = false } = {}) {
  status('Reading the page…', 'busy');
  let tab = null;
  try { tab = await activeTab(); } catch { /* no tab */ }
  S.tabId = tab && tab.id; S.tabUrl = (tab && tab.url) || '';
  const p = tab ? await readPage(tab) : null;
  await applyPage(p || { ok: false, error: 'Open a problem on leetcode.com or geeksforgeeks.org, or paste code below.' }, { keepCode });
  status('');
  cx.schedule(100);
  if (auto && p && p.ok !== false && p.code && p.code.trim().length > 15) {
    if (S.examples.length) runAll();
    else status('Problem read. No example input found in the statement — type an input and press Visualize.');
  }
}

let debounce = null;
function onTabChange(url) { clearTimeout(debounce); debounce = setTimeout(() => { if (url !== S.tabUrl || !S.page) refresh({ auto: true }); }, 700); }

function init() {
  cx = createComplexityPanel({ root: $('cxCard'), getSource: cxSource, getRunInfo: cxRunInfo, onJump: cxJump });
  $('btnRefresh').onclick = () => refresh({ auto: true });
  $('btnRun').onclick = runAll;
  $('exSel').onchange = () => { pickExample(); };
  $('inputBox').oninput = () => { S.expectedKnown = false; $('exSel').value = '-1'; };
  $('codeBox').oninput = () => { S.userEdited = true; cx.schedule(); };
  $('inputBox').addEventListener('input', () => cx.schedule(900));
  $('refBox').addEventListener('input', () => cx.schedule());
  $('langSel').onchange = () => { warmIfPython(); cx.schedule(100); };
  $('refBox').oninput = () => { if (S.mode === 'correct') $('refBlock').hidden = false; };
  document.querySelectorAll('#modeSeg button').forEach((b) => { b.onclick = () => { setMode(b.dataset.mode, Boolean(S.trace) || b.dataset.mode === 'correct'); }; });
  $('bPlay').onclick = togglePlay;
  $('bNext').onclick = () => { stopPlay(); S.step++; renderStep(); };
  $('bPrev').onclick = () => { stopPlay(); S.step--; renderStep(); };
  $('bReset').onclick = () => { stopPlay(); S.step = 0; renderStep(); };
  $('slider').oninput = () => { stopPlay(); S.step = Number($('slider').value); renderStep(); };
  $('speedSel').onchange = () => { if (S.playing) { clearTimeout(S.timer); S.timer = setTimeout(tick, 900 / Number($('speedSel').value)); } };
  document.addEventListener('keydown', (e) => {
    if (/TEXTAREA|INPUT|SELECT/.test(document.activeElement.tagName) && e.key !== 'Escape') { if (document.activeElement.type !== 'range') return; }
    if (!S.trace) return;
    if (e.key === ' ') { e.preventDefault(); togglePlay(); } else if (e.key === 'ArrowRight') { stopPlay(); S.step++; renderStep(); } else if (e.key === 'ArrowLeft') { stopPlay(); S.step--; renderStep(); } else if (e.key === 'Home') { stopPlay(); S.step = 0; renderStep(); }
  });
  if (typeof chrome !== 'undefined' && chrome.tabs) {
    chrome.tabs.onActivated.addListener(async (i) => { try { const t = await chrome.tabs.get(i.tabId); onTabChange(t.url); } catch {} });
    chrome.tabs.onUpdated.addListener((id, info, t) => { if (t.active && (info.status === 'complete' || info.url)) onTabChange(t.url); });
  }
  refresh({ auto: true });
}
function warmIfPython() { if ($('langSel').value === 'python') warmupPython(); }
window.__codeTalk = { get cx() { return cx; }, S, runAll, refresh, goTo, setMode };
init();
