// Step view: code, explanation, variables, pattern cards, call tree, call stack. Pure rendering from (trace, analysis, step index).
import { h } from './dom.js';
import { renderValue, isRect, renderMatrix, renderArray, renderGraph, renderCallTree, scalarText } from './render.js';
import { show, fmt, shapeOf } from '../analysis/analyze.js';

const isObj = (v) => v && typeof v === 'object' && !Array.isArray(v);
const J = JSON.stringify;

// ---------------------------------------------------------------- syntax colouring (tiny, per line)
const KW = {
  cpp: 'int long short char bool double float void auto const static class struct public private protected return if else for while do break continue new delete true false nullptr NULL using namespace template typename vector string unordered_map map set unordered_set stack queue deque priority_queue pair sizeof switch case default',
  java: 'int long short char boolean double float void final static class public private protected return if else for while do break continue new true false null import switch case default this extends implements interface String List Map Set ArrayList HashMap HashSet',
  python: 'def class return if elif else for while in not and or is None True False import from as with try except finally raise pass break continue lambda yield global nonlocal self',
};
export function highlight(line, lang) {
  const kws = new Set((KW[lang] || KW.cpp).split(' '));
  const frag = document.createDocumentFragment();
  const re = /(\/\/.*|#.*)|("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*')|(\b\d+(?:\.\d+)?\b)|([A-Za-z_]\w*)/g;
  let last = 0, m;
  while ((m = re.exec(line))) {
    if (m.index > last) frag.append(line.slice(last, m.index));
    const [txt, cm, st, nu, id] = m;
    if (cm && (m[0][0] !== '#' || lang === 'python')) frag.append(h('span', { class: 'cm' }, txt));
    else if (cm) frag.append(txt);
    else if (st) frag.append(h('span', { class: 'st' }, txt));
    else if (nu) frag.append(h('span', { class: 'nu' }, txt));
    else if (id && kws.has(id)) frag.append(h('span', { class: 'kw' }, txt));
    else frag.append(txt);
    last = m.index + txt.length;
  }
  if (last < line.length) frag.append(line.slice(last));
  return frag;
}

// ---------------------------------------------------------------- tiny safe expression evaluator for index expressions
export function evalIdx(src, env) {
  const toks = src.match(/\d+|[A-Za-z_]\w*|[-+*/%()]|\/\//g);
  if (!toks) return undefined;
  let p = 0;
  const peek = () => toks[p];
  function prim() {
    const t = toks[p++];
    if (t === undefined) throw new Error('eof');
    if (t === '(') { const v = add(); if (toks[p++] !== ')') throw new Error('paren'); return v; }
    if (t === '-') return -prim();
    if (/^\d+$/.test(t)) return Number(t);
    if (t in env && typeof env[t] === 'number') return env[t];
    throw new Error('unknown');
  }
  function mul() { let v = prim(); while (['*', '/', '%', '//'].includes(peek())) { const o = toks[p++]; const r = prim(); v = o === '*' ? v * r : o === '%' ? v % r : Math.trunc(v / r); } return v; }
  function add() { let v = mul(); while (['+', '-'].includes(peek())) { const o = toks[p++]; const r = mul(); v = o === '+' ? v + r : v - r; } return v; }
  try { const v = add(); return p === toks.length && Number.isFinite(v) ? v : undefined; } catch { return undefined; }
}

function mdInline(text) {
  const frag = document.createDocumentFragment();
  const re = /(\*\*[^*]+\*\*|`[^`]+`)/g;
  let last = 0, m;
  while ((m = re.exec(text))) {
    if (m.index > last) frag.append(text.slice(last, m.index));
    const t = m[0];
    frag.append(t.startsWith('**') ? h('b', null, t.slice(2, -2)) : h('code', null, t.slice(1, -1)));
    last = m.index + t.length;
  }
  if (last < text.length) frag.append(text.slice(last));
  return frag;
}

// ---------------------------------------------------------------- helpers over the trace
function visibleVars(s, m) {
  const v = {};
  if (m && m.ctx) Object.assign(v, m.ctx);
  Object.assign(v, s.members || {}, s.vars || {});
  return v;
}
function cellSets(change) {
  const set = new Set();
  if (!change || !change.cells) return set;
  for (const c of change.cells) set.add(c.idx.join(','));
  return set;
}
function findChange(list, name) { return (list || []).find((c) => c.name === name); }
function pointerMap(name, vars, hints, len) {
  const dims = hints.pointers[name];
  const out = {};
  if (!dims || !dims[0]) return out;
  for (const nm of dims[0]) { const v = vars[nm]; if (typeof v === 'number' && Number.isInteger(v) && v >= 0 && v <= len && nm !== name) (out[v] ||= []).push(nm); }
  return out;
}

/** Nodes seen so far (latest record wins): lets a recursive call draw the WHOLE tree, not just its own subtree. */
function mergedHeap(trace, i) {
  const out = {};
  for (let k = Math.max(0, i - 500); k <= i; k++) { const h2 = trace.steps[k].heap; if (h2) Object.assign(out, h2); }
  return out;
}
function topOf(heap, addr) {
  const parent = {};
  for (const [a, n] of Object.entries(heap)) for (const f of ['left', 'right']) if (n[f] && heap[n[f]]) (parent[n[f]] ||= a);
  let cur = addr; const seen = new Set();
  while (parent[cur] && !seen.has(cur)) { seen.add(cur); cur = parent[cur]; }
  return cur;
}

/** Find the most recent earlier value of `name` (used to highlight changes of structures that live in caller frames). */
function previousValue(trace, i, name) {
  for (let k = i - 1; k >= 0 && k > i - 400; k--) { const s = trace.steps[k]; const bag = (s.vars && name in s.vars) ? s.vars : (s.members && name in s.members ? s.members : null); if (bag) return bag[name]; }
  return undefined;
}

function diffCells(a, b) {
  const set = new Set();
  if (!Array.isArray(a) || !Array.isArray(b)) return set;
  b.forEach((v, i) => { if (Array.isArray(v)) { v.forEach((x, j) => { if (!Array.isArray(a[i]) || J(a[i][j]) !== J(x)) set.add(`${i},${j}`); }); } else if (J(a[i]) !== J(v)) set.add(String(i)); });
  return set;
}

// ---------------------------------------------------------------- pieces
export function renderCode(el, state) {
  const { lines, lang, trace, step, errorLine } = state;
  if (el.dataset.key !== state.codeKey) {
    el.dataset.key = state.codeKey;
    el.textContent = '';
    const hit = new Set(trace.steps.map((s) => s.line));
    lines.forEach((L, i) => {
      el.append(h('div', { class: `ln ${hit.has(i + 1) ? 'hit' : ''}`, 'data-n': i + 1 }, h('span', { class: 'no' }, String(i + 1)), h('span', { class: 'src' }, highlight(L || ' ', lang))));
    });
  }
  const s = trace.steps[step];
  el.querySelectorAll('.ln.cur,.ln.err').forEach((n) => n.classList.remove('cur', 'err'));
  const row = s ? el.querySelector(`.ln[data-n="${s.line}"]`) : null;
  if (row) { row.classList.add(s.ev === 'error' ? 'err' : 'cur'); const top = row.offsetTop - el.clientHeight / 2 + 10; if (Math.abs(el.scrollTop - top) > el.clientHeight / 3) el.scrollTo({ top, behavior: 'smooth' }); }
  if (errorLine) { const er = el.querySelector(`.ln[data-n="${errorLine}"]`); if (er) er.classList.add('hot'); }
}

export function renderExplain(el, state) {
  const { trace, an, step } = state;
  const s = trace.steps[step]; const m = an.meta[step];
  el.textContent = '';
  if (!s) return;
  const ex = m.explain;
  const head = h('div', null, h('span', { class: 'tag' }, ex.title));
  if (m.cond === true) head.append(h('span', { class: 'tag true' }, 'TRUE'));
  if (m.cond === false) head.append(h('span', { class: 'tag false' }, 'FALSE'));
  head.append(h('span', { class: 'note' }, `line ${s.line}`));
  el.append(head, h('div', { class: 'body' }, mdInline(ex.text)));
  if (ex.before) el.append(h('div', { class: 'before' }, mdInline(ex.before)));
  if (ex.warn) el.append(h('div', { class: 'warn' }, `⚠ ${ex.warn}`));
}

function varCard(name, v, ctx) {
  const { vars, heapLabels, changeList, effectList, hints, trace, step, s, m, shared } = ctx;
  const ch = findChange(changeList, name);
  const ef = findChange(effectList, name);
  const opts = { changed: cellSets(ch), will: cellSets(ef) };
  if (shared) { const prev = previousValue(trace, step, name); if (prev !== undefined && J(prev) !== J(v)) { opts.changed = diffCells(prev, v); if (isObj(v) && v.$ === 'map') opts.changedKeys = new Set(v.e.map(([k, x]) => [k, x]).filter(([k, x]) => { const pm = isObj(prev) && prev.$ === 'map' ? prev.e.find(([pk]) => J(pk) === J(k)) : null; return !pm || J(pm[1]) !== J(x); }).map(([k]) => J(k))); } }
  if (ch && ch.keys) opts.changedKeys = new Set(ch.keys.map((k) => J(k.key)));
  if (ch && (ch.added || ch.removed)) opts.added = new Set((ch.added || []).map(J));
  let body;
  if (Array.isArray(v) && !v.some(Array.isArray)) opts.pointers = pointerMap(name, vars, hints, v.length);
  if (typeof v === 'string' && v.length > 0) {
    const ptr = pointerMap(name, vars, hints, v.length);
    body = h('div', null, h('span', { class: 'scalar string' }, JSON.stringify(v).slice(0, 80)), Object.keys(ptr).length || v.length <= 40 ? renderStringRow(v, ptr) : null);
  } else if (isRect(v)) {
    const dims = hints.pointers[name];
    if (dims && dims[1]) { const r = dims[0].map((n) => vars[n]).find((x) => Number.isInteger(x)); const c = dims[1].map((n) => vars[n]).find((x) => Number.isInteger(x)); if (r !== undefined && c !== undefined) opts.cursor = [[r, c]]; }
    body = renderMatrix(v, opts);
  } else body = renderValue(v, opts, trace.steps[step].heap || {});
  const tags = [];
  if (ch) tags.push(h('span', { class: 'chg' }, 'changed'));
  if (ch === undefined && opts.changed && opts.changed.size) tags.push(h('span', { class: 'chg' }, 'changed'));
  return h('div', { class: 'var' }, h('div', { class: 'vname' }, name, h('span', { class: 'kind' }, kindLabel(v)), tags), body);
}

function renderStringRow(v, ptr) {
  const row = h('div', { class: 'arr str' });
  [...v].slice(0, 60).forEach((c, i) => row.append(h('div', { class: 'col' }, h('div', { class: `cell ${ptr[i] ? 'ptr' : ''}` }, h('span', { class: 'cv' }, c === ' ' ? '␣' : c)), h('div', { class: 'idx' }, String(i)), h('div', { class: 'ptrs' }, (ptr[i] || []).join(' ')))));
  return row;
}

function kindLabel(v) {
  const k = shapeOf(v);
  if (k === 'int') return 'int'; if (k === 'num') return 'number'; if (k === 'string') return `string(${v.length})`;
  if (k === 'array') return `list(${v.length})`; if (k === 'matrix') return `${v.length}×${(v[0] || []).length} table`;
  if (k === 'map') return `map(${v.n ?? v.e.length})`; if (k === 'set') return `set(${v.n ?? v.e.length})`;
  if (k === 'ref') return v.k === 'TreeNode' ? 'tree' : 'linked list';
  if (['stack', 'queue', 'deque', 'pq'].includes(k)) return `${k}(${v.n ?? v.e.length})`;
  return typeof v === 'boolean' ? 'bool' : '';
}

export function renderVars(el, noteEl, state) {
  const { trace, an, step } = state;
  const s = trace.steps[step]; const m = an.meta[step];
  el.textContent = '';
  if (!s) return;
  const heap = mergedHeap(trace, step);
  const vars = visibleVars(s, m);
  const hints = an.hints;
  const nextI = (() => { for (let j = step + 1; j < trace.steps.length; j++) if (trace.steps[j].fid === s.fid) return j; return -1; })();
  void nextI;
  const ctx = { vars, hints, trace, step, s, m, changeList: m.changes, effectList: m.effect, heapLabels: null };
  const own = Object.entries({ ...(s.members || {}), ...(s.vars || {}) });
  // pointer-linked structures: one drawing per structure, with variable names attached to nodes
  const refVars = own.filter(([, v]) => isObj(v) && v.$ === 'ref');
  const labels = {};
  for (const [n, v] of refVars) (labels[v.a] ||= []).push(n);
  const reach = (a) => { const seen = new Set(); const st = [a]; while (st.length) { const x = st.pop(); if (!x || seen.has(x) || !heap[x]) continue; seen.add(x); for (const f of ['next', 'left', 'right']) st.push(heap[x][f]); } return seen; };
  const reaches = refVars.map(([n, v]) => ({ n, a: v.a, r: reach(v.a) }));
  const drawn = new Set();
  const groups = [];
  for (const g of [...reaches].sort((a, b) => b.r.size - a.r.size)) {
    if (drawn.has(g.n)) continue;
    const members = reaches.filter((o) => g.r.has(o.a));
    members.forEach((o) => drawn.add(o.n)); drawn.add(g.n);
    groups.push({ root: g.a, names: [g.n, ...members.map((o) => o.n)].filter((x, i, a) => a.indexOf(x) === i), kind: heap[g.a] ? heap[g.a].k : '' });
  }
  const done = new Set();
  const order = [];
  for (const [name, v] of own) {
    if (isObj(v) && v.$ === 'ref') {
      if (done.has(name)) continue;
      const g = groups.find((x) => x.names.includes(name));
      if (!g) continue;
      if (g.kind === 'TreeNode') g.top = topOf(heap, g.root);
      g.names.forEach((n) => done.add(n));
      order.push(['struct', g]);
    } else order.push(['var', name, v]);
  }
  for (const item of order) {
    if (item[0] === 'struct') {
      const g = item[1];
      const body = renderValue({ $: 'ref', a: g.top || g.root, k: g.kind }, { labels }, heap);
      const changed = (m.changes || []).some((c) => c.kind === 'link' || g.names.includes(c.name));
      el.append(h('div', { class: 'var' }, h('div', { class: 'vname' }, g.names.join(', '), h('span', { class: 'kind' }, g.kind === 'TreeNode' ? 'binary tree' : 'linked list'), changed ? h('span', { class: 'chg' }, 'changed') : null), body));
    } else el.append(varCard(item[1], item[2], ctx));
  }
  const sharedNames = Object.keys(m.ctx || {});
  if (sharedNames.length) {
    el.append(h('div', { class: 'note', style: { marginTop: '8px' } }, 'Shared with the calling code (changed by this call too):'));
    for (const n of sharedNames) el.append(varCard(n, m.ctx[n], { ...ctx, shared: true }));
  }
  if (!el.childNodes.length) el.append(h('div', { class: 'empty' }, 'No variables yet.'));
  noteEl.textContent = `state before line ${s.line} runs`;
}

function readsAndTarget(line, name, env) {
  const reads = new Set(); let target = null;
  const re = new RegExp(`\\b${name.replace(/[$]/g, '\\$')}\\s*((?:\\[[^\\]\\n]*\\]\\s*)+)`, 'g');
  let m;
  while ((m = re.exec(line))) {
    const brs = (m[1].match(/\[([^\]]*)\]/g) || []).map((b) => b.slice(1, -1));
    const idx = brs.map((b) => evalIdx(b, env));
    if (idx.some((x) => x === undefined)) continue;
    const after = line.slice(m.index + m[0].length);
    const isTarget = /^\s*(?:[-+*/%|&^]|<<|>>)?=(?!=)/.test(after) && !line.slice(0, m.index).includes('=');
    if (isTarget) target = idx.join(','); else reads.add(idx.join(','));
  }
  return { reads, target };
}

export function renderHints(el, state) {
  const { trace, an, step, code } = state;
  const s = trace.steps[step]; const m = an.meta[step];
  el.textContent = '';
  if (!s) return;
  const vars = visibleVars(s, m);
  const hints = an.hints;
  const line = (state.lines[s.line - 1] || '');
  const env = {}; for (const [k, v] of Object.entries(vars)) if (typeof v === 'number') env[k] = v;
  const card = (title, basis, body) => el.append(h('div', { class: 'card hintcard' }, h('div', { class: 'chead' }, title, h('span', { class: 'basis' }, basis)), body));

  for (const d of hints.dp) {
    const v = vars[d.name]; if (v === undefined) continue;
    const ch = findChange(m.changes, d.name); const ef = findChange(m.effect, d.name);
    let changed = cellSets(ch);
    if (!ch && m.ctx && d.name in m.ctx) { const pv = previousValue(trace, step, d.name); if (pv !== undefined) changed = diffCells(pv, v); }
    const { reads, target } = readsAndTarget(line, d.name, env);
    const opts = { changed, will: cellSets(ef), reads, ...{} };
    if (target && Array.isArray(v)) { if (Array.isArray(v[0])) opts.will = new Set([...opts.will, target]); else opts.will = new Set([...opts.will, target]); }
    const body = h('div', null, isRect(v) ? renderMatrix(v, opts) : isObj(v) && v.$ === 'map' ? renderValue(v, { changedKeys: new Set((ch && ch.keys || []).map((k) => J(k.key))) }) : renderArray(v, { ...opts, pointers: pointerMap(d.name, vars, hints, v.length) }),
      h('div', { class: 'note', style: { marginTop: '4px' } }, 'yellow = just written, blue dashed = this line writes here, green = cells this line reads'));
    card(`DP table · ${d.name}`, 'detected from code, values are real', body);
  }
  for (const g of hints.grids) {
    const v = vars[g.name]; if (!isRect(v)) continue;
    const r = g.rowVars.map((n) => vars[n]).find((x) => Number.isInteger(x));
    const c = g.colVars.map((n) => vars[n]).find((x) => Number.isInteger(x));
    const ch = findChange(m.changes, g.name);
    let changed = cellSets(ch);
    if (!ch) { const pv = previousValue(trace, step, g.name); if (pv !== undefined && m.ctx && g.name in m.ctx) changed = diffCells(pv, v); }
    const visited = Object.entries(vars).find(([n, x]) => n !== g.name && /(visited|seen|vis)/i.test(n) && Array.isArray(x) && x.length === v.length && Array.isArray(x[0]));
    const heat = visited ? null : null;
    void heat;
    const opts = { changed, will: cellSets(findChange(m.effect, g.name)), cursor: r !== undefined && c !== undefined ? [[r, c]] : [], rowMark: r, colMark: c };
    if (visited) { const vm = visited[1]; opts.heat = null; opts.reads = new Set(); vm.forEach((row, i) => row.forEach((x, j) => { if (x === true || (typeof x === 'number' && x > 0)) opts.reads.add(`${i},${j}`); })); }
    const extra = visited ? h('div', { class: 'note', style: { marginTop: '4px' } }, `green outline = cells marked in ${visited[0]}`) : null;
    card(`Grid · ${g.name}`, 'detected from code, values are real', h('div', null, renderMatrix(v, opts), extra));
  }
  for (const g of hints.graphs) {
    const v = vars[g.name]; if (v === undefined) continue;
    const data = graphData(g, v, vars, code, hints);
    if (data) card(`Graph · ${g.name}`, 'detected from code, values are real', renderGraph(data));
  }
  for (const b of hints.backtrack) {
    const v = vars[b.name]; if (v === undefined) continue;
    const arr = typeof v === 'string' ? [...v] : Array.isArray(v) ? v : isObj(v) ? v.e : [];
    const ch = findChange(m.changes, b.name);
    let op = null;
    if (ch && ch.cells && ch.cells.length === 1) op = ch.cells[0].op === 'add' ? 'choose' : ch.cells[0].op === 'remove' ? 'undo' : null;
    else if (ch && typeof ch.from === 'string' && typeof ch.to === 'string') op = ch.to.length > ch.from.length ? 'choose' : ch.to.length < ch.from.length ? 'undo' : null;
    const path = h('div', { class: 'path' }, h('span', { class: 'note' }, 'path:'), ...(arr.length ? arr.map((x, i) => h('span', { class: `chip ${i === arr.length - 1 && op === 'choose' ? 'new' : ''}` }, scalarText(x))) : [h('span', { class: 'empty' }, '(empty)')]));
    if (op === 'undo' && ch) path.append(h('span', { class: 'chip undo' }, scalarText((ch.cells && ch.cells[0].from) ?? ch.from.slice(-1))));
    const msg = op === 'choose' ? 'Just CHOSE an item (added to the path)' : op === 'undo' ? 'Just UN-CHOSE the last item (backtracked)' : 'The path is explored depth-first: choose → recurse → un-choose';
    card(`Backtracking · ${b.name}`, 'detected from code, values are real', h('div', null, path, h('div', { class: 'note', style: { marginTop: '4px' } }, msg), res(vars)));
  }
}
function res(vars) {
  const r = Object.entries(vars).find(([n, v]) => /^(res|result|ans|answer|results|output)$/i.test(n) && Array.isArray(v));
  return r ? h('div', { class: 'note', style: { marginTop: '4px' } }, `${r[0]} so far: ${show(r[1], 90)}`) : null;
}

function graphData(g, v, vars, code, hints) {
  let n = 0, edges = [];
  if (g.kind === 'adj' && Array.isArray(v)) { n = v.length; v.forEach((nb, u) => (Array.isArray(nb) ? nb : []).forEach((x) => { const t = Array.isArray(x) ? x[0] : x; if (Number.isInteger(t)) edges.push([u, t]); })); }
  else if (g.kind === 'dict' && isObj(v) && v.$ === 'map') {
    const keys = v.e.map(([k]) => k);
    if (!keys.every(Number.isInteger)) return null;
    n = Math.max(...keys, -1) + 1; v.e.forEach(([u, nb]) => (Array.isArray(nb) ? nb : []).forEach((t) => { if (Number.isInteger(t)) { edges.push([u, t]); n = Math.max(n, t + 1); } }));
  } else if (g.kind === 'edges' && Array.isArray(v)) {
    edges = v.filter((e) => Array.isArray(e) && Number.isInteger(e[0]) && Number.isInteger(e[1])).map((e) => [e[0], e[1]]);
    const nv = ['n', 'V', 'numCourses', 'numNodes', 'N'].map((k) => vars[k]).find((x) => Number.isInteger(x));
    n = Math.max(nv || 0, ...edges.flat(), -1) + 1;
    if (nv && edges.some((e) => e[0] === nv || e[1] === nv)) n = nv + 1;
  }
  if (!n) return null;
  const directed = !edges.every(([a, b]) => edges.some(([c, d]) => c === b && d === a)) || g.kind === 'edges';
  const hot = new Set(); const labels = {};
  const idxUse = (nm) => new RegExp(`\\b(?:${g.name}|visited|seen|vis|color|state|indeg\\w*|dist|parent|dp)\\s*\\[\\s*${nm}\\b`).test(code);
  for (const [nm, x] of Object.entries(vars)) if (Number.isInteger(x) && x >= 0 && x < n && nm !== g.name && idxUse(nm)) hot.add(x);
  let labelVar = null;
  for (const [nm, x] of Object.entries(vars)) {
    if (nm === g.name || !/(visit|seen|vis|color|dist|indeg|parent|state)/i.test(nm)) continue;
    if (Array.isArray(x) && x.length === n && x.every((e) => !Array.isArray(e) && !isObj(e))) { x.forEach((e, i) => { labels[i] = e === true ? '✓' : e === false ? '' : e; }); labelVar = nm; break; }
  }
  const frontier = new Set();
  for (const [, x] of Object.entries(vars)) if (isObj(x) && ['queue', 'stack', 'deque', 'pq'].includes(x.$)) x.e.forEach((e) => { const t = Array.isArray(e) ? e[0] : isObj(e) && e.$ === 'tuple' ? e.e[0] : e; if (Number.isInteger(t)) frontier.add(t); });
  void hints; void labelVar;
  return { n, edges, directed, hot, frontier, labels };
}

export function renderStack(el, state) {
  const { trace, an, step } = state;
  const s = trace.steps[step];
  el.textContent = '';
  if (!s) return;
  const chain = [];
  let f = an.frames.find((x) => x.fid === s.fid);
  const byId = new Map(an.frames.map((x) => [x.fid, x]));
  while (f) { chain.push(f); f = byId.get(f.pfid); }
  chain.forEach((fr, i) => el.append(h('div', { class: `frame ${i === 0 ? 'cur' : ''}` }, h('span', { class: 'd' }, `#${fr.depth}`), `${fr.fn}(${fr.args || ''})`, i === 0 ? h('span', { class: 'note' }, ' ← running') : null)));
}

export function renderCalls(card, el, state, jump) {
  const { trace, an, step } = state;
  const s = trace.steps[step];
  if (!an.hints.recursive) { card.hidden = true; return; }
  const view = renderCallTree(an.frames, s ? s.fid : -1, step, jump);
  if (!view) { card.hidden = true; return; }
  card.hidden = false; el.textContent = ''; el.append(view);
}

export { visibleVars, mdInline };
