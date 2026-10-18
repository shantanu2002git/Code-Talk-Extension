// Renderers: turn trace values into DOM (arrays, matrices, maps, sets, stacks, queues, linked lists, trees, graphs, call tree).
import { h, svg } from './dom.js';
import { fmt, show, shapeOf } from '../analysis/analyze.js';

const isObj = (v) => v && typeof v === 'object' && !Array.isArray(v);
const J = JSON.stringify;

export function scalarText(v) {
  if (v === null || v === undefined) return 'null';
  if (typeof v === 'string') return v === '' ? '""' : v;
  if (typeof v === 'boolean' || typeof v === 'number') return String(v);
  if (isObj(v)) {
    if (v.$ === 'chr') return `'${v.s}'`;
    if (v.$ === 'dbl') return `${v.v}.0`;
    if (v.$ === 'uninit') return '?';
  }
  return fmt(v);
}
const isScalar = (v) => v === null || ['string', 'number', 'boolean'].includes(typeof v) || (isObj(v) && ['chr', 'dbl', 'uninit'].includes(v.$));

function cell(v, cls = '') { return h('div', { class: `cell ${cls}`, title: fmt(v) }, h('span', { class: 'cv' }, scalarText(v).slice(0, 8))); }

/** opts: {changed:Set('i' | 'i,j'), will:Set, pointers:{idx:[names]}, ptrCells:Set} */
export function renderArray(arr, opts = {}) {
  const trunc = isObj(arr) && arr.$ === 'trunc';
  const items = trunc ? arr.e : arr;
  if (!items.length) return h('div', { class: 'empty' }, 'empty []');
  if (items.every(isScalar)) {
    const row = h('div', { class: 'arr' });
    items.forEach((v, i) => {
      const ptrs = (opts.pointers && opts.pointers[i]) || [];
      const cls = [opts.changed && opts.changed.has(String(i)) ? 'changed' : '', opts.will && opts.will.has(String(i)) ? 'will' : '', ptrs.length ? 'ptr' : '', opts.mark && opts.mark.has(i) ? 'mark' : ''].join(' ');
      row.append(h('div', { class: 'col' }, cell(v, cls), h('div', { class: 'idx' }, String(i)), h('div', { class: 'ptrs' }, ptrs.join(' '))));
    });
    if (trunc) row.append(h('div', { class: 'more' }, `… ${arr.n} items`));
    return row;
  }
  // array of non scalars
  const wrap = h('div', { class: 'stackv' });
  items.forEach((v, i) => wrap.append(h('div', { class: 'row-item' }, h('span', { class: 'idx' }, `[${i}]`), renderValue(v, {}))));
  return wrap;
}

export function renderMatrix(m, opts = {}) {
  const rows = m.length;
  const cols = Math.max(...m.map((r) => (Array.isArray(r) ? r.length : 0)), 0);
  if (cols > 30 || rows > 30) return h('div', { class: 'empty' }, `${rows}×${cols} table (too large to draw) — first row: ${show(m[0], 80)}`);
  const t = h('table', { class: 'mat' });
  const head = h('tr', null, h('th', null, ''));
  for (let c = 0; c < cols; c++) head.append(h('th', { class: opts.colMark === c ? 'hot' : '' }, String(c)));
  t.append(head);
  m.forEach((r, i) => {
    const tr = h('tr', null, h('th', { class: opts.rowMark === i ? 'hot' : '' }, String(i)));
    (Array.isArray(r) ? r : []).forEach((v, j) => {
      const k = `${i},${j}`;
      const cls = [opts.changed && opts.changed.has(k) ? 'changed' : '', opts.will && opts.will.has(k) ? 'will' : '', opts.cursor && opts.cursor.some(([a, b]) => a === i && b === j) ? 'cursor' : '', opts.reads && opts.reads.has(k) ? 'reads' : ''].join(' ');
      const val = scalarText(v);
      const style = opts.heat ? { background: opts.heat(v) } : null;
      tr.append(h('td', { class: cls, title: `[${i}][${j}] = ${fmt(v)}`, style }, val.slice(0, 6)));
    });
    t.append(tr);
  });
  return h('div', { class: 'matwrap' }, t);
}

function renderMap(m, opts = {}) {
  if (!m.e.length) return h('div', { class: 'empty' }, 'empty map {}');
  const t = h('table', { class: 'map' });
  m.e.forEach(([k, v]) => {
    const ch = opts.changedKeys && opts.changedKeys.has(J(k));
    t.append(h('tr', { class: ch ? 'changed' : '' }, h('td', { class: 'k' }, scalarText(k)), h('td', { class: 'arrow' }, '→'), h('td', { class: 'v' }, isScalar(v) ? scalarText(v) : renderValue(v, {}))));
  });
  if (m.n > m.e.length) t.append(h('tr', null, h('td', { colspan: 3 }, `… ${m.n} entries`)));
  return t;
}

function renderSet(s, opts = {}) {
  if (!s.e.length) return h('div', { class: 'empty' }, 'empty set {}');
  const w = h('div', { class: 'chips' });
  s.e.forEach((x) => w.append(h('span', { class: `chip ${opts.added && opts.added.has(J(x)) ? 'changed' : ''}` }, scalarText(x))));
  return w;
}

function renderSeq(v, opts = {}) {
  const kind = v.$;
  const e = v.e;
  const wrap = h('div', { class: `seq ${kind}` });
  if (!e.length) return h('div', { class: 'empty' }, `empty ${kind}`);
  const items = e.map((x, i) => h('div', { class: `seqitem ${opts.added && opts.added.has(J(x)) && i === (kind === 'stack' ? e.length - 1 : -1) ? 'changed' : ''}` }, isScalar(x) ? scalarText(x) : show(x, 22)));
  if (kind === 'stack') { // top is the last item: show it on top
    wrap.append(h('div', { class: 'tag' }, 'top ▼'), ...[...items].reverse());
  } else {
    wrap.classList.add('horiz');
    wrap.append(h('div', { class: 'tag' }, kind === 'pq' ? 'next out →' : 'front →'), ...items, h('div', { class: 'tag' }, kind === 'queue' || kind === 'deque' ? '← back' : ''));
  }
  return wrap;
}

export function renderString(s, opts = {}) {
  const chars = [...s].slice(0, 80);
  const row = h('div', { class: 'arr str' });
  chars.forEach((c, i) => {
    const ptrs = (opts.pointers && opts.pointers[i]) || [];
    row.append(h('div', { class: 'col' }, h('div', { class: `cell ${ptrs.length ? 'ptr' : ''} ${opts.changed && opts.changed.has(String(i)) ? 'changed' : ''}` }, h('span', { class: 'cv' }, c === ' ' ? '␣' : c)), h('div', { class: 'idx' }, String(i)), h('div', { class: 'ptrs' }, ptrs.join(' '))));
  });
  return row;
}

export const isRect = (v) => Array.isArray(v) && v.length > 0 && v.every((r) => Array.isArray(r) && r.length === v[0].length && r.length > 0);

function renderJagged(v, opts) {
  const wrap = h('div', { class: 'stackv' });
  v.slice(0, 40).forEach((r, i) => wrap.append(h('div', { class: 'row-item' }, h('span', { class: 'idx' }, `[${i}]`), Array.isArray(r) ? (r.length ? renderArray(r, { changed: opts.changed && new Set([...opts.changed].filter((k) => k.startsWith(`${i},`)).map((k) => k.split(',')[1])) }) : h('span', { class: 'empty' }, '[ ]')) : renderValue(r, {}))));
  if (v.length > 40) wrap.append(h('div', { class: 'more' }, `… ${v.length} rows`));
  return wrap;
}

export function renderValue(v, opts = {}, heap = {}) {
  if (v === null || v === undefined) return h('span', { class: 'scalar nul' }, 'null');
  if (isScalar(v)) return h('span', { class: `scalar ${typeof v}` }, scalarText(v));
  if (Array.isArray(v)) {
    if (v.length && v.every((r) => Array.isArray(r)) && !opts.noMatrix) return isRect(v) ? renderMatrix(v, opts) : renderJagged(v, opts);
    return renderArray(v, opts);
  }
  switch (v.$) {
    case 'trunc': return renderArray(v, opts);
    case 'map': return renderMap(v, opts);
    case 'set': return renderSet(v, opts);
    case 'stack': case 'queue': case 'deque': case 'pq': return renderSeq(v, opts);
    case 'tuple': return h('span', { class: 'tuple' }, `(${v.e.map(scalarText).join(', ')})`);
    case 'ref': return renderStructure([v.a], heap, opts.labels || {}, v.k);
    case 'obj': return h('div', { class: 'objv' }, h('div', { class: 'objt' }, v.t), ...Object.entries(v.f).map(([k, x]) => h('div', { class: 'objf' }, h('span', { class: 'k' }, k), renderValue(x, {}, heap))));
    case 'cycle': return h('span', { class: 'scalar' }, '(cycle)');
    default: return h('span', { class: 'scalar' }, fmt(v));
  }
}

// ---------------------------------------------------------------- linked lists & trees
/** Draw the node structures reachable from `roots`. labels: addr -> [variable names pointing there]. */
export function renderStructure(roots, heap, labels, kind) {
  const wrap = h('div', { class: 'structs' });
  const seenRoots = new Set();
  for (const r of roots) {
    if (!r || seenRoots.has(r) || !heap[r]) continue;
    seenRoots.add(r);
    const k = heap[r].k;
    wrap.append(k === 'TreeNode' ? renderTree(r, heap, labels) : renderList(r, heap, labels));
  }
  if (!wrap.childNodes.length) wrap.append(h('span', { class: 'scalar nul' }, 'null'));
  return wrap;
}

function renderList(root, heap, labels) {
  const row = h('div', { class: 'llist' });
  const seen = new Set();
  let a = root;
  while (a && heap[a] && !seen.has(a)) {
    seen.add(a);
    const n = heap[a];
    const lab = labels[a] || [];
    row.append(h('div', { class: 'lnode' }, h('div', { class: 'lab' }, lab.join(' ')), h('div', { class: `lbox ${lab.length ? 'ptr' : ''}` }, h('span', { class: 'val' }, scalarText(n.val)), h('span', { class: 'nx' }, n.next ? '•' : '∅')), ), h('div', { class: 'larrow' }, n.next ? (seen.has(n.next) ? '↺' : '→') : ''));
    a = n.next;
    if (seen.size > 60) { row.append(h('span', { class: 'more' }, '…')); break; }
  }
  if (a && seen.has(a)) row.append(h('span', { class: 'more' }, `(cycle back to ${scalarText(heap[a].val)})`));
  else row.append(h('div', { class: 'lnode' }, h('div', { class: 'lab' }, ''), h('div', { class: 'lnull' }, 'null')));
  return row;
}

function renderTree(root, heap, labels) {
  const pos = new Map();
  let counter = 0, maxD = 0;
  const seen = new Set();
  (function walk(a, d) {
    if (!a || !heap[a] || seen.has(a)) return;
    seen.add(a);
    walk(heap[a].left, d + 1);
    pos.set(a, { x: counter++, y: d });
    maxD = Math.max(maxD, d);
    walk(heap[a].right, d + 1);
  })(root, 0);
  const dx = 34, dy = 44, pad = 20;
  const W = Math.max(counter * dx + pad, 60), H = (maxD + 1) * dy + 22;
  const s = svg('svg', { class: 'tree', width: W, height: H, viewBox: `0 0 ${W} ${H}` });
  const P = (a) => ({ x: pad / 2 + pos.get(a).x * dx + dx / 2, y: 22 + pos.get(a).y * dy });
  for (const [a] of pos) for (const f of ['left', 'right']) { const c = heap[a][f]; if (c && pos.has(c)) { const p = P(a), q = P(c); s.append(svg('line', { x1: p.x, y1: p.y, x2: q.x, y2: q.y, class: 'edge' })); } }
  for (const [a] of pos) {
    const p = P(a);
    const lab = labels[a] || [];
    s.append(svg('circle', { cx: p.x, cy: p.y, r: 13, class: `tnode ${lab.length ? 'ptr' : ''}` }), svg('text', { x: p.x, y: p.y + 4, class: 'tval', 'text-anchor': 'middle' }, scalarText(heap[a].val).slice(0, 4)));
    if (lab.length) s.append(svg('text', { x: p.x, y: p.y - 17, class: 'tlab', 'text-anchor': 'middle' }, lab.join(' ').slice(0, 14)));
  }
  return h('div', { class: 'treewrap' }, s);
}

// ---------------------------------------------------------------- graph
export function renderGraph(data, cur) {
  // data: {n, edges:[[u,v]], directed, labels:{node:text}, hot:Set, frontier:Set}
  const n = data.n;
  if (!n || n > 40) return h('div', { class: 'empty' }, `Graph with ${n} nodes is too large to draw.`);
  const R = Math.max(50, Math.min(110, n * 12));
  const W = R * 2 + 60, H = R * 2 + 50;
  const s = svg('svg', { class: 'graph', width: W, height: H, viewBox: `0 0 ${W} ${H}` });
  const pt = (i) => { const a = (2 * Math.PI * i) / n - Math.PI / 2; return { x: W / 2 + R * Math.cos(a), y: H / 2 + R * Math.sin(a) }; };
  s.append(svg('defs', null, svg('marker', { id: 'arr', markerWidth: 8, markerHeight: 8, refX: 7, refY: 3, orient: 'auto' }, svg('path', { d: 'M0,0 L7,3 L0,6 z', class: 'arrowhead' }))));
  for (const [u, v] of data.edges) {
    if (u === v || u >= n || v >= n || u < 0 || v < 0) continue;
    const p = pt(u), q = pt(v);
    const L = Math.hypot(q.x - p.x, q.y - p.y) || 1;
    const ex = q.x - ((q.x - p.x) / L) * (data.directed ? 17 : 0), ey = q.y - ((q.y - p.y) / L) * (data.directed ? 17 : 0);
    s.append(svg('line', { x1: p.x, y1: p.y, x2: ex, y2: ey, class: 'edge', 'marker-end': data.directed ? 'url(#arr)' : null }));
  }
  for (let i = 0; i < n; i++) {
    const p = pt(i);
    const cls = ['gnode', data.hot && data.hot.has(i) ? 'cursor' : '', data.frontier && data.frontier.has(i) ? 'front' : '', data.done && data.done.has(i) ? 'done' : ''].join(' ');
    s.append(svg('circle', { cx: p.x, cy: p.y, r: 14, class: cls }), svg('text', { x: p.x, y: p.y + 4, class: 'tval', 'text-anchor': 'middle' }, String(i)));
    if (data.labels && data.labels[i] !== undefined) s.append(svg('text', { x: p.x, y: p.y + 27, class: 'tlab', 'text-anchor': 'middle' }, String(data.labels[i]).slice(0, 8)));
  }
  void cur;
  return h('div', { class: 'treewrap' }, s);
}

// ---------------------------------------------------------------- call tree
export function renderCallTree(frames, curFid, curStep, onPick) {
  const vis = frames.filter((f) => f.first <= curStep);
  if (vis.length < 2) return null;
  const MAXN = 90;
  const all = frames.slice(0, 400);
  const byId = new Map(all.map((f) => [f.fid, f]));
  const kids = new Map();
  for (const f of all) { if (!kids.has(f.pfid)) kids.set(f.pfid, []); kids.get(f.pfid).push(f); }
  if (all.length <= MAXN) {
    // tidy tree: x by leaf slots
    let slot = 0; const pos = new Map(); let maxD = 0;
    (function lay(f, d) {
      maxD = Math.max(maxD, d);
      const ks = (kids.get(f.fid) || []);
      if (!ks.length) { pos.set(f.fid, { x: slot++, y: d }); return; }
      ks.forEach((k) => lay(k, d + 1));
      pos.set(f.fid, { x: (pos.get(ks[0].fid).x + pos.get(ks[ks.length - 1].fid).x) / 2, y: d });
    })(all.find((f) => !byId.has(f.pfid)), 0);
    const dx = 62, dy = 50, pad = 30;
    const W = Math.max(slot * dx + pad, 120), H = (maxD + 1) * dy + 20;
    const s = svg('svg', { class: 'calltree', width: W, height: H, viewBox: `0 0 ${W} ${H}` });
    const P = (f) => ({ x: pad / 2 + pos.get(f.fid).x * dx + dx / 2, y: 24 + pos.get(f.fid).y * dy });
    for (const f of all) { const p = byId.get(f.pfid); if (p && pos.has(f.fid) && pos.has(p.fid)) { const a = P(p), b = P(f); s.append(svg('line', { x1: a.x, y1: a.y, x2: b.x, y2: b.y, class: `edge ${f.first <= curStep ? '' : 'future'}` })); } }
    for (const f of all) {
      if (!pos.has(f.fid)) continue;
      const p = P(f);
      const state = f.first > curStep ? 'future' : f.fid === curFid ? 'current' : f.end >= curStep && f.first <= curStep ? 'active' : 'done';
      const g = svg('g', { class: `cnode ${state}`, style: 'cursor:pointer' }, svg('rect', { x: p.x - 28, y: p.y - 15, width: 56, height: 30, rx: 8 }), svg('text', { x: p.x, y: p.y - 2, 'text-anchor': 'middle', class: 'ct1' }, (f.label || f.fn).slice(0, 10)), svg('text', { x: p.x, y: p.y + 10, 'text-anchor': 'middle', class: 'ct2' }, f.hasRet && f.retStep <= curStep ? (f.ret === null || f.ret === undefined ? '✓' : `→ ${show(f.ret, 7)}`) : ''));
      g.append(svg('title', null, `${f.fn}(${f.args || ''})${f.hasRet ? ` → ${fmt(f.ret)}` : ''}`));
      g.addEventListener('click', () => onPick(f.first));
      s.append(g);
    }
    return h('div', { class: 'treewrap' }, s);
  }
  // large: indented list of the calls that already started
  const list = h('div', { class: 'ctlist' });
  const walk = (f, d) => {
    if (f.first > curStep || list.childNodes.length > 160) return;
    list.append(h('div', { class: `ctrow ${f.fid === curFid ? 'current' : ''}`, style: { paddingLeft: `${Math.min(d, 14) * 10}px`, cursor: 'pointer' }, onclick: () => onPick(f.first) }, `${f.fn}(${f.label || ''})`, f.hasRet && f.retStep <= curStep ? ` → ${show(f.ret, 20)}` : ''));
    (kids.get(f.fid) || []).forEach((k) => walk(k, d + 1));
  };
  all.filter((f) => !byId.has(f.pfid)).forEach((f) => walk(f, 0));
  return list;
}

export { shapeOf };
