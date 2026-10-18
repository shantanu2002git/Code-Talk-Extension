// Turns a raw execution trace into what the panel shows: per-step "what changed" (real diffs between consecutive
// states), plain-language explanations, the recursion call tree, shared structures from caller frames and
// pattern hints (DP table, grid, graph, backtracking). Nothing here invents states: every value comes from the trace;
// pattern detection only decides HOW to draw real values and is labelled "inferred".

const J = (v) => JSON.stringify(v);
const isObj = (v) => v && typeof v === 'object' && !Array.isArray(v);
const esc = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const isNum = (v) => typeof v === 'number';

export function show(v, max = 60) {
  const s = fmt(v);
  return s.length > max ? s.slice(0, max - 1) + '…' : s;
}
export function fmt(v) {
  if (v === null || v === undefined) return 'null';
  if (typeof v === 'string') return JSON.stringify(v);
  if (typeof v === 'number' || typeof v === 'boolean') return String(v);
  if (Array.isArray(v)) return `[${v.map(fmt).join(', ')}]`;
  switch (v.$) {
    case 'chr': return `'${v.s}'`;
    case 'dbl': return `${v.v}.0`;
    case 'uninit': return '(uninitialised)';
    case 'ref': return v.k === 'TreeNode' ? 'a tree node' : 'a list node';
    case 'tuple': return `(${v.e.map(fmt).join(', ')})`;
    case 'map': return `{${v.e.map(([k, x]) => `${fmt(k)}: ${fmt(x)}`).join(', ')}}`;
    case 'set': return `{${v.e.map(fmt).join(', ')}}`;
    case 'stack': case 'queue': case 'deque': case 'pq': return `${v.$}[${v.e.map(fmt).join(', ')}]`;
    case 'obj': return `${v.t}(${Object.entries(v.f).map(([k, x]) => `${k}=${fmt(x)}`).join(', ')})`;
    case 'trunc': return `[${v.e.map(fmt).join(', ')}, … ${v.n} items]`;
    case 'cycle': return '(cycle)';
    default: return v.s !== undefined ? String(v.s) : '?';
  }
}

export function indentOf(line) { const m = /^[\t ]*/.exec(line)[0]; return m.replace(/\t/g, '    ').length; }

// ---------------------------------------------------------------- diffs
function cellDiffs(a, b) {
  const out = [];
  if (Array.isArray(a) && Array.isArray(b)) {
    const n = Math.max(a.length, b.length);
    for (let i = 0; i < n; i++) {
      if (i >= a.length) out.push({ idx: [i], to: b[i], op: 'add' });
      else if (i >= b.length) out.push({ idx: [i], from: a[i], op: 'remove' });
      else if (J(a[i]) !== J(b[i])) {
        if (Array.isArray(a[i]) && Array.isArray(b[i])) for (const d of cellDiffs(a[i], b[i])) out.push({ ...d, idx: [i, ...d.idx] });
        else out.push({ idx: [i], from: a[i], to: b[i], op: 'set' });
      }
      if (out.length > 40) break;
    }
  }
  return out;
}

function diffValue(a, b) {
  if (J(a) === J(b)) return null;
  const d = { from: a, to: b };
  if (Array.isArray(a) && Array.isArray(b)) d.cells = cellDiffs(a, b);
  else if (isObj(a) && isObj(b) && a.$ === 'map' && b.$ === 'map') {
    const A = new Map(a.e.map(([k, v]) => [J(k), v])); const B = new Map(b.e.map(([k, v]) => [J(k), v]));
    d.keys = [];
    for (const [k, v] of B) if (!A.has(k)) d.keys.push({ key: JSON.parse(k), op: 'add', to: v }); else if (J(A.get(k)) !== J(v)) d.keys.push({ key: JSON.parse(k), op: 'set', from: A.get(k), to: v });
    for (const [k, v] of A) if (!B.has(k)) d.keys.push({ key: JSON.parse(k), op: 'remove', from: v });
  } else if (isObj(a) && isObj(b) && a.$ === 'set' && b.$ === 'set') {
    const A = new Set(a.e.map(J)); const B = new Set(b.e.map(J));
    d.added = b.e.filter((x) => !A.has(J(x))); d.removed = a.e.filter((x) => !B.has(J(x)));
  } else if (isObj(a) && isObj(b) && a.e && b.e && a.$ === b.$) {
    d.added = b.e.length > a.e.length ? b.e.slice(a.e.length) : []; d.removed = a.e.length > b.e.length ? a.e.slice(b.e.length) : [];
  }
  return d;
}

/** Real differences between two consecutive states of one frame (and of the pointer-linked nodes they reach). */
export function diffStates(prev, cur) {
  const changes = [];
  if (!cur) return changes;
  const pv = prev ? prev.vars : {};
  for (const [name, v] of Object.entries(cur.vars || {})) {
    if (!(name in pv)) { changes.push({ name, kind: 'new', to: v }); continue; }
    const d = diffValue(pv[name], v);
    if (d) changes.push({ name, kind: 'changed', ...d });
  }
  if (cur.members) for (const [name, v] of Object.entries(cur.members)) {
    const was = prev && prev.members ? prev.members[name] : undefined;
    const d = was === undefined ? { from: undefined, to: v } : diffValue(was, v);
    if (d) changes.push({ name, kind: was === undefined ? 'new' : 'changed', member: true, ...d });
  }
  // node-level changes in linked lists / trees (a pointer was rewired or a value was edited)
  const ph = (prev && prev.heap) || {}; const ch = cur.heap || {};
  for (const [a, n] of Object.entries(ch)) {
    const o = ph[a];
    if (!o) continue;
    for (const f of ['val', 'next', 'left', 'right']) {
      if (J(o[f]) !== J(n[f])) changes.push({ name: `${nodeName(ch, a)}.${f}`, kind: 'link', node: a, field: f, from: f === 'val' ? o[f] : nodeName(ph, o[f]), to: f === 'val' ? n[f] : nodeName(ch, n[f]) });
    }
  }
  return changes;
}
function nodeName(heap, a) { if (!a) return 'null'; const n = heap[a]; return n ? `node(${fmt(n.val)})` : 'null'; }

// ---------------------------------------------------------------- code line classification & explanation
export function lineKind(text) {
  const t = text.trim();
  if (!t) return 'blank';
  if (/^(?:\}\s*)?else\s+if\b|^elif\b/.test(t)) return 'elif';
  if (/^(?:\}\s*)?else\b/.test(t)) return 'else';
  if (/^if\b/.test(t)) return 'if';
  if (/^for\b/.test(t)) return 'for';
  if (/^while\b/.test(t)) return 'while';
  if (/^do\b/.test(t)) return 'do';
  if (/^return\b/.test(t)) return 'return';
  if (/^break\b/.test(t)) return 'break';
  if (/^continue\b/.test(t)) return 'continue';
  if (/^(?:def|class)\b/.test(t)) return 'def';
  if (/^(?:throw|raise)\b/.test(t)) return 'throw';
  if (/^(?:assert)\b/.test(t)) return 'assert';
  if (/^[})\]]+[;,]?$/.test(t) || t === '{') return 'brace';
  return 'stmt';
}

function condText(text, kind) {
  let t = text.trim().replace(/^\}\s*/, '');
  if (kind === 'if' || kind === 'elif') {
    t = t.replace(/^(?:else\s+if|elif|if)\s*/, '');
    if (t.startsWith('(')) { const m = matchParen(t); if (m) return t.slice(1, m); }
    return t.replace(/:\s*$/, '').replace(/\{\s*$/, '').trim();
  }
  if (kind === 'while') { t = t.replace(/^while\s*/, ''); if (t.startsWith('(')) { const m = matchParen(t); if (m) return t.slice(1, m); } return t.replace(/:\s*$/, '').replace(/\{\s*$/, '').trim(); }
  if (kind === 'for') {
    const m = /^for\s*\((.*)\)\s*\{?\s*$/.exec(t);
    if (m) { const parts = m[1].split(';'); if (parts.length === 3) return parts[1].trim(); return m[1].trim(); }
    return t.replace(/^for\s+/, '').replace(/:\s*$/, '');
  }
  return t;
}
function matchParen(s) { let d = 0; for (let i = 0; i < s.length; i++) { if (s[i] === '(') d++; else if (s[i] === ')') { d--; if (d === 0) return i; } } return 0; }

/** Python: a condition is "true" when the next executed line of the same call is indented deeper than the test line. */
export function inferPyCond(steps, i, lines) {
  const s = steps[i];
  const kind = lineKind(lines[s.line - 1] || '');
  if (!['if', 'elif', 'while'].includes(kind)) return null;
  for (let j = i + 1; j < steps.length; j++) {
    const n = steps[j];
    if (n.fid !== s.fid) continue;
    if (n.ev === 'error') return null;
    if (n.line === s.line) return n.ev === 'return' && /:\s*return\b/.test(lines[s.line - 1] || '') ? true : null;
    const a = indentOf(lines[s.line - 1] || ''); const b = indentOf(lines[n.line - 1] || '');
    return b > a;
  }
  return null;
}

function refVal(v, heap) { const n = heap && heap[v.a]; return n ? show(n.val, 8) : '?'; }
function scalarList(vars, max = 4, heap = null) {
  return Object.entries(vars || {}).filter(([, v]) => !isObj(v) || ['chr', 'dbl'].includes(v.$) || (v.$ === 'ref' && heap)).slice(0, max).map(([k, v]) => (isObj(v) && v.$ === 'ref' ? `${k}=node(${refVal(v, heap)})` : `${k}=${show(v, 14)}`)).join(', ');
}

function describeChange(c) {
  if (c.kind === 'link') return c.field === 'val' ? `${c.name} changes from ${fmt(c.from)} to ${fmt(c.to)}` : `${c.name} now points to ${c.to} (was ${c.from})`;
  if (c.kind === 'new') return `\`${c.name}\` is created = ${show(c.to, 50)}`;
  if (c.cells && c.cells.length && c.cells.length <= 4) return c.cells.map((x) => (x.op === 'add' ? `\`${c.name}\` gets a new item ${show(x.to, 24)} at position ${x.idx.join(',')}` : x.op === 'remove' ? `\`${c.name}\` loses item ${show(x.from, 24)} at position ${x.idx.join(',')}` : `\`${c.name}[${x.idx.join('][')}]\` changes ${show(x.from, 20)} → ${show(x.to, 20)}`)).join('; ');
  if (c.keys && c.keys.length && c.keys.length <= 3) return c.keys.map((x) => (x.op === 'add' ? `\`${c.name}\` gets key ${show(x.key, 20)} → ${show(x.to, 20)}` : x.op === 'remove' ? `\`${c.name}\` drops key ${show(x.key, 20)}` : `\`${c.name}[${show(x.key, 14)}]\` changes ${show(x.from, 16)} → ${show(x.to, 16)}`)).join('; ');
  if (c.added && c.added.length && !(c.removed && c.removed.length)) return `\`${c.name}\` gains ${c.added.map((x) => show(x, 16)).join(', ')}`;
  if (c.removed && c.removed.length && !(c.added && c.added.length)) return `\`${c.name}\` loses ${c.removed.map((x) => show(x, 16)).join(', ')}`;
  return `\`${c.name}\`: ${show(c.from, 28)} → ${show(c.to, 28)}`;
}

export function describeChanges(changes, max = 4) {
  const parts = changes.slice(0, max).map(describeChange);
  if (changes.length > max) parts.push(`and ${changes.length - max} more`);
  return parts.join('; ');
}

// ---------------------------------------------------------------- main
export function analyze({ steps, code, lang }) {
  const lines = String(code || '').replace(/\r/g, '').split('\n');
  const lastByFid = new Map();
  const meta = new Array(steps.length);
  const frames = new Map();
  const nextSameFrame = new Array(steps.length).fill(-1);
  const lastIdx = new Map();
  for (let i = steps.length - 1; i >= 0; i--) { const f = steps[i].fid; nextSameFrame[i] = lastIdx.has(f) ? lastIdx.get(f) : -1; lastIdx.set(f, i); }

  // ---- frames
  steps.forEach((s, i) => {
    let f = frames.get(s.fid);
    if (!f) { f = { fid: s.fid, pfid: s.pfid, fn: s.fn, depth: s.depth, first: i, last: i, ret: undefined, hasRet: false }; frames.set(s.fid, f); }
    f.last = i;
    if (s.ev === 'return') { f.ret = s.ret; f.hasRet = true; f.retStep = i; }
    if (s.ev === 'error') f.failed = true;
  });
  for (const f of frames.values()) {
    const first = steps[f.first];
    f.args = scalarList(first.vars, 4, first.heap);
    f.label = Object.values(first.vars || {}).filter((v) => v === null || ['number', 'string', 'boolean'].includes(typeof v) || (isObj(v) && (['chr', 'dbl'].includes(v.$) || v.$ === 'ref'))).slice(0, 3).map((v) => (isObj(v) && v.$ === 'ref' ? refVal(v, first.heap) : show(v, 6).replace(/^"|"$/g, ''))).join(',');
    f.argVars = first.vars;
  }
  // a call lasts until the last step of any descendant
  const order = [...frames.values()];
  for (const f of [...order].reverse()) { const p = frames.get(f.pfid); if (p) p.end = Math.max(p.end || 0, f.end || f.last, f.last); }
  for (const f of order) f.end = Math.max(f.end || 0, f.last);
  const kids = new Map();
  for (const f of order) { if (!kids.has(f.pfid)) kids.set(f.pfid, []); kids.get(f.pfid).push(f.fid); }
  for (const f of order) { f.children = (kids.get(f.fid) || []).length; f.quick = !f.children && f.last - f.first <= 3 && f.depth > 1; }

  // ---- hints
  const hints = detectPatterns(steps, lines, frames, lang);

  // ---- shared context from caller frames
  const ctxNames = new Set(hints.shared);
  const latest = new Map();

  steps.forEach((s, i) => {
    const prev = lastByFid.get(s.fid);
    const m = {};
    m.changes = prev ? diffStates(prev, s) : [];
    m.firstOfCall = !prev;
    // condition
    const text = lines[s.line - 1] || '';
    const kind = lineKind(text);
    let cond = s.cond;
    if (cond === undefined && lang === 'python') cond = inferPyCond(steps, i, lines);
    m.cond = cond === undefined ? null : cond;
    m.kind = kind;
    // lookahead: what this line does
    const j = nextSameFrame[i];
    const nxt = j >= 0 ? steps[j] : null;
    m.effect = nxt && nxt.ev !== 'error' ? diffStates(s, nxt).filter((c) => c.kind !== 'new' || true) : [];
    m.callsInto = i + 1 < steps.length && steps[i + 1].pfid === s.fid && steps[i + 1].fid !== s.fid ? steps[i + 1].fid : null;
    m.explain = explainStep(s, i, steps, m, text, kind, lines, lang, frames);
    // shared structures (names that live in caller frames and are not visible in this frame)
    const ctx = {};
    for (const nm of ctxNames) { if (!(s.vars && nm in s.vars) && !(s.members && nm in s.members) && latest.has(nm)) ctx[nm] = latest.get(nm); }
    if (Object.keys(ctx).length) m.ctx = ctx;
    for (const bag of [s.vars, s.members]) for (const [k, v] of Object.entries(bag || {})) if (ctxNames.has(k)) latest.set(k, v);
    lastByFid.set(s.fid, s);
    meta[i] = m;
  });

  return { meta, frames: order, hints, lines };
}

function explainStep(s, i, steps, m, text, kind, lines, lang, frames) {
  const t = text.trim();
  const fr = frames.get(s.fid);
  const callTag = s.depth > 1 || (fr && fr.children) ? ` (call ${s.fn}(${fr ? fr.args : ''}))` : '';
  if (s.ev === 'error') return { title: 'Error', text: s.message || 'The program stopped with an error here.', tone: 'bad' };
  if (s.ev === 'return') {
    const r = s.ret === undefined ? 'nothing' : show(s.ret, 60);
    return { title: 'Return', text: s.depth > 1 ? `\`${s.fn}\` finishes and gives back **${r}** to its caller.` : `The function finishes and returns **${r}**.`, tone: 'ok' };
  }
  let title = 'Run line', body = '';
  const changedNow = m.changes.length ? describeChanges(m.changes) : '';
  const eff = m.effect && m.effect.length ? describeChanges(m.effect) : '';
  const cond = m.cond;
  switch (kind) {
    case 'if': case 'elif': {
      title = kind === 'if' ? 'Decision' : 'Else-if decision';
      const c = condText(t, kind);
      body = cond === null ? `Evaluates the condition \`${c}\`.` : cond ? `Condition \`${c}\` is **true**, so the indented block runs.` : `Condition \`${c}\` is **false**, so this block is skipped.`;
      break;
    }
    case 'else': title = 'Else branch'; body = 'No earlier condition was true, so the else-branch runs.'; break;
    case 'while': case 'do': {
      title = 'Loop check';
      const c = condText(t, kind);
      body = cond === null ? `Checks the loop condition \`${c}\`.` : cond ? `Loop condition \`${c}\` is **true** → run the loop body again.` : `Loop condition \`${c}\` is **false** → the loop ends.`;
      break;
    }
    case 'for': {
      title = 'Loop';
      const c = condText(t, 'for');
      if (cond === false) body = `The loop condition \`${c}\` is **false** → the loop ends.`;
      else if (cond === true) body = `Loop condition \`${c}\` is **true** → run the body.`;
      else {
        // Python-style for: the next step of the same call tells whether the body ran
        const j = steps.findIndex((x, k) => k > i && x.fid === s.fid);
        const n = j >= 0 ? steps[j] : null;
        if (n && n.line !== s.line && indentOf(lines[n.line - 1] || '') > indentOf(text)) body = `Takes the next item${eff ? ` (${eff})` : ''} and enters the loop body.`;
        else if (n && n.line === s.line) body = `Runs the loop header \`${c}\`.`;
        else body = 'No items left, so the loop finishes.';
      }
      break;
    }
    case 'break': title = 'Break'; body = 'Leaves the loop immediately.'; break;
    case 'continue': title = 'Continue'; body = 'Skips the rest of this iteration and goes to the next one.'; break;
    case 'return': {
      title = 'Return';
      const nx = steps[m.callsInto !== null ? i + 1 : i + 1];
      void nx;
      body = `Evaluates \`${t.replace(/^return\s*/, '').replace(/;$/, '') || 'nothing'}\` and returns it${m.callsInto !== null ? ' (first it must call a function)' : ''}.`;
      break;
    }
    case 'throw': title = 'Throw'; body = 'Raises an exception here.'; break;
    case 'def': title = 'Definition'; body = 'Defines a function or class (nothing runs yet).'; break;
    case 'brace': title = 'Block end'; body = 'End of a block; execution continues after it.'; break;
    default: {
      title = 'Statement';
      if (m.callsInto !== null) {
        const callee = steps[i + 1];
        body = `Calls \`${callee.fn}(${scalarList(callee.vars, 5, callee.heap)})\` — a new call frame opens (depth ${callee.depth}).`;
      } else if (eff) body = `This line executes: ${eff}.`;
      else body = `Executes \`${t.replace(/;$/, '')}\`${' '.length ? '.' : ''}`;
    }
  }
  const out = { title, text: body, tone: cond === false ? 'muted' : 'info' };
  if (changedNow && kind !== 'brace') out.before = `Since the previous line: ${changedNow}.`;
  if (callTag && s.depth > 1 && m.firstOfCall) out.text = `A new call starts: \`${s.fn}(${fr.args})\`. ${body}`;
  if (s.warn) out.warn = s.warn;
  return out;
}

// ---------------------------------------------------------------- patterns
function seqOf(x) { return typeof x === 'string' ? [...x] : Array.isArray(x) ? x : (isObj(x) && ['stack', 'deque'].includes(x.$) ? x.e : null); }
function stackOp(prev, next) {
  if (prev === undefined) return null;
  const a = seqOf(prev), b = seqOf(next);
  if (!a || !b || Math.abs(a.length - b.length) !== 1) return null;
  const [sh, lg] = a.length < b.length ? [a, b] : [b, a];
  for (let i = 0; i < sh.length; i++) if (J(sh[i]) !== J(lg[i])) return null;
  return a.length < b.length ? 'push' : 'pop';
}

const DP_NAME = /(dp|memo|cache|table|ways|best)/i;
const GRID_NAME = /(grid|board|maze|image|land|^mat|matrix|heights|forest|dungeon|field|cells|island|terrain|rooms)/i;
const ADJ_NAME = /(graph|adj|neigh|nbr|children|connections|edges|^g$)/i;

function detectPatterns(steps, lines, frames, lang) {
  const code = lines.join('\n');
  const names = new Map(); // name -> {kinds:Set, frames:Set(fid), maxLen}
  const note = (k, v, fid) => {
    let e = names.get(k); if (!e) { e = { kinds: new Set(), fids: new Set() }; names.set(k, e); }
    e.fids.add(fid);
    e.kinds.add(shapeOf(v));
  };
  for (const s of steps) for (const bag of [s.vars, s.members]) for (const [k, v] of Object.entries(bag || {})) note(k, v, s.fid);
  const maxDepth = steps.reduce((m, s) => Math.max(m, s.depth || 1), 1);

  // index pointers per array: names used inside arr[...]
  const idxNames = {};
  for (const nm of names.keys()) {
    const re = new RegExp(`\\b${esc(nm)}\\s*((?:\\[[^\\]\\n]*\\]\\s*)+)`, 'g');
    let m; const dims = [];
    while ((m = re.exec(code))) {
      const brs = m[1].match(/\[[^\]]*\]/g) || [];
      brs.forEach((b, d) => { dims[d] = dims[d] || new Set(); for (const id of b.match(/[A-Za-z_]\w*/g) || []) dims[d].add(id); });
    }
    // Python: dict/list access with .get / in
    if (dims.length) idxNames[nm] = dims.map((s) => [...s]);
  }

  // DP tables: arrays / maps written by index where the right side reads the same table, or named like dp
  const dp = [];
  for (const [nm, e] of names) {
    if (!(e.kinds.has('array') || e.kinds.has('matrix') || e.kinds.has('map'))) continue;
    const writes = [], selfRef = [];
    lines.forEach((L, k) => {
      const m = new RegExp(`\\b${esc(nm)}\\s*(?:\\[[^\\]\\n]*\\]\\s*)+(?:[-+*/%|&^]|<<|>>)?=(?!=)(.*)`).exec(L);
      if (m) { writes.push(k + 1); if (new RegExp(`\\b${esc(nm)}\\s*\\[`).test(m[1])) selfRef.push(k + 1); }
    });
    const reads = new RegExp(`\\b${esc(nm)}\\s*\\[`).test(code);
    if (writes.length && (selfRef.length || DP_NAME.test(nm)) && reads) dp.push({ name: nm, dims: e.kinds.has('matrix') ? 2 : e.kinds.has('map') ? 'map' : 1, writes: writes.length, why: selfRef.length ? 'cells are computed from other cells of the same table' : 'a table named like a DP / memo and written by index' });
  }
  dp.sort((a, b) => b.writes - a.writes);
  const dpTop = dp.slice(0, 2);
  const dpNames = new Set(dpTop.map((d) => d.name));

  // grids
  const hasDirs = /(\bdirs?\b|\bdirections?\b|\bdx\b|\bdy\b|\{\s*0\s*,\s*1\s*\}|\[\s*0\s*,\s*1\s*\]|\{\s*-1\s*,\s*0\s*\}|\[\s*-1\s*,\s*0\s*\])/.test(code);
  const grids = [];
  for (const [nm, e] of names) {
    if (!e.kinds.has('matrix') || dpNames.has(nm)) continue;
    if (/(visited|seen|vis|dist|memo|dp)/i.test(nm) && !GRID_NAME.test(nm)) continue;
    const idx = idxNames[nm];
    if ((GRID_NAME.test(nm) || hasDirs) && idx && idx.length >= 2) grids.push({ name: nm, rowVars: idx[0], colVars: idx[1] });
  }
  // graphs
  const graphs = [];
  for (const [nm, e] of names) {
    if (dpNames.has(nm) || grids.some((g) => g.name === nm)) continue;
    if ((e.kinds.has('matrix') || e.kinds.has('map')) && ADJ_NAME.test(nm)) graphs.push({ name: nm, kind: e.kinds.has('map') ? 'dict' : 'adj' });
    else if (e.kinds.has('matrix') && /(edge|prereq|connection|road|flight|times|relation|trust|route|pairs)/i.test(nm)) graphs.push({ name: nm, kind: 'edges' });
  }
  // backtracking: one-element push/pop on the same name inside the same frame
  const bt = [];
  if (maxDepth >= 2) {
    const cnt = new Map(); const last = new Map();
    for (const s of steps) for (const bag of [s.vars, s.members]) for (const [k, v] of Object.entries(bag || {})) {
      if (!(Array.isArray(v) || typeof v === 'string' || (isObj(v) && ['stack', 'deque'].includes(v.$)))) continue;
      const key = `${s.fid}|${k}`;
      const op = stackOp(last.get(key), v);
      last.set(key, v);
      if (op) { const c = cnt.get(k) || { push: 0, pop: 0 }; c[op]++; cnt.set(k, c); }
    }
    for (const [k, c] of cnt) if (c.push && c.pop) bt.push({ name: k, ...c });
    bt.sort((a, b) => b.push + b.pop - a.push - a.pop);
  }
  // names that live in caller frames and are mutated / read by callees: show them in callee views too
  const shared = new Set();
  if (maxDepth >= 2) {
    for (const [nm, e] of names) {
      const structural = e.kinds.has('array') || e.kinds.has('matrix') || e.kinds.has('map') || e.kinds.has('set');
      if (structural && (dpNames.has(nm) || bt.some((b) => b.name === nm) || /^(res|result|ans|answer|memo|dp|cache|visited|seen|path|board|grid)$/i.test(nm))) shared.add(nm);
    }
  }
  const pointerNames = {};
  for (const [nm, dims] of Object.entries(idxNames)) pointerNames[nm] = dims.map((d) => d.slice(0, 6));
  return {
    dp: dpTop.map((d) => ({ ...d, basis: 'inferred' })),
    grids: grids.slice(0, 2).map((g) => ({ ...g, basis: 'inferred' })),
    graphs: graphs.slice(0, 2).map((g) => ({ ...g, basis: 'inferred' })),
    backtrack: bt.slice(0, 3).map((b) => ({ ...b, basis: 'inferred' })),
    shared: [...shared],
    pointers: pointerNames,
    recursive: maxDepth >= 2,
    maxDepth,
    totalCalls: frames.size,
  };
}

function shapeOf(v) {
  if (Array.isArray(v)) return v.length && v.every((x) => Array.isArray(x)) ? 'matrix' : 'array';
  if (isObj(v)) { if (v.$ === 'map') return 'map'; if (v.$ === 'set') return 'set'; if (v.$ === 'ref') return 'ref'; if (['stack', 'queue', 'deque', 'pq'].includes(v.$)) return v.$; return 'other'; }
  if (typeof v === 'string') return 'string';
  if (typeof v === 'number') return Number.isInteger(v) ? 'int' : 'num';
  return 'scalar';
}
export { shapeOf };
