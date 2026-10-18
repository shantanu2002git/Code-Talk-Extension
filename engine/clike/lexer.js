// Lexer shared by the C++ and Java front ends. Produces tokens with 1-based line numbers (kept exact so the
// trace can point at real source lines).

const OPS = [
  '>>>=', '<<=', '>>=', '>>>', '->*', '...', '<=>',
  '->', '::', '++', '--', '&&', '||', '==', '!=', '<=', '>=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<', '>>',
  '+', '-', '*', '/', '%', '=', '<', '>', '!', '~', '&', '|', '^', '?', ':', ';', ',', '.', '(', ')', '[', ']', '{', '}', '@', '#',
];

export class LexError extends Error {
  constructor(message, line) { super(message); this.line = line; this.kind = 'syntax'; }
}

const ALT = { and: '&&', or: '||', not: '!', xor: '^', bitand: '&', bitor: '|', compl: '~', not_eq: '!=', and_eq: '&=', or_eq: '|=', xor_eq: '^=' };
const isIdStart = (c) => /[A-Za-z_$]/.test(c);
const isIdPart = (c) => /[A-Za-z0-9_$]/.test(c);

export function lex(src, lang) {
  const toks = [];
  const defines = new Map(); // object-like #define NAME tokens
  let i = 0, line = 1;
  const n = src.length;
  const push = (t, v, extra = {}) => toks.push({ t, v, line, ...extra });
  while (i < n) {
    const c = src[i];
    if (c === '\n') { line++; i++; continue; }
    if (c === ' ' || c === '\t' || c === '\r' || c === '\f' || c === '\u00a0' || c === '\u200b' || c === '\ufeff' || /[\u2000-\u200a\u202f\u3000]/.test(c)) { i++; continue; }
    // comments
    if (c === '/' && src[i + 1] === '/') { while (i < n && src[i] !== '\n') i++; continue; }
    if (c === '/' && src[i + 1] === '*') {
      i += 2;
      while (i < n && !(src[i] === '*' && src[i + 1] === '/')) { if (src[i] === '\n') line++; i++; }
      i += 2;
      continue;
    }
    // preprocessor (C++): skip, remember simple object-like #define
    if (c === '#' && lang === 'cpp') {
      let j = i;
      let text = '';
      while (j < n && src[j] !== '\n') {
        if (src[j] === '\\' && src[j + 1] === '\n') { j += 2; line++; continue; }
        if (src[j] === '/' && src[j + 1] === '/') { while (j < n && src[j] !== '\n') j++; break; }
        text += src[j++];
      }
      const m = /^#\s*define\s+([A-Za-z_]\w*)(\(.*?\))?\s*(.*)$/.exec(text.trim());
      if (m && !m[2]) defines.set(m[1], m[3].trim());
      i = j;
      continue;
    }
    // identifiers
    if (isIdStart(c)) {
      let j = i + 1;
      while (j < n && isIdPart(src[j])) j++;
      const word = src.slice(i, j);
      i = j;
      if (defines.has(word) && lang === 'cpp') {
        const sub = lex(defines.get(word), lang).toks.filter((x) => x.t !== 'eof');
        for (const s of sub) toks.push({ ...s, line });
      } else if (lang === 'cpp' && ALT[word] && !/^[.]|->$/.test('')) push('op', ALT[word]);
      else push('id', word);
      continue;
    }
    // numbers
    if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(src[i + 1] || ''))) {
      let j = i;
      let text;
      let isFloat = false;
      if (c === '0' && /[xX]/.test(src[i + 1] || '')) {
        j = i + 2;
        while (j < n && /[0-9a-fA-F_']/.test(src[j])) j++;
        text = src.slice(i, j).replace(/['_]/g, '');
      } else if (c === '0' && /[bB]/.test(src[i + 1] || '') && /[01]/.test(src[i + 2] || '')) {
        j = i + 2;
        while (j < n && /[01_']/.test(src[j])) j++;
        text = src.slice(i, j).replace(/['_]/g, '');
      } else {
        while (j < n && /[0-9_']/.test(src[j])) j++;
        if (src[j] === '.' && /[0-9]/.test(src[j + 1] || '') ) { isFloat = true; j++; while (j < n && /[0-9_']/.test(src[j])) j++; }
        else if (src[j] === '.' && !/[A-Za-z_.]/.test(src[j + 1] || '')) { isFloat = true; j++; }
        if (/[eE]/.test(src[j] || '') && /[0-9+\-]/.test(src[j + 1] || '')) {
          isFloat = true; j++;
          if (/[+\-]/.test(src[j])) j++;
          while (j < n && /[0-9]/.test(src[j])) j++;
        }
        text = src.slice(i, j).replace(/['_]/g, '');
      }
      let suffix = '';
      while (j < n && /[uUlLfFdD]/.test(src[j])) suffix += src[j++];
      i = j;
      const s = suffix.toLowerCase();
      const hex = /^0[xXbB]/.test(text);
      if (!hex && (isFloat || s.includes('f') || s.includes('d'))) push('num', Number(text), { kind: 'double' });
      else {
        let big;
        try { big = BigInt(/^0[0-7]+$/.test(text) ? `0o${text.slice(1)}` : text); } catch { throw new LexError(`Bad number "${text}"`, line); }
        const unsigned = s.includes('u');
        const isLong = s.includes('l') || (big > 2147483647n && !(unsigned && big <= 4294967295n));
        push('num', big, { kind: isLong ? 'long' : unsigned ? 'uint' : 'int' });
      }
      continue;
    }
    // strings
    if (c === '"') {
      let j = i + 1, out = '';
      // Java text blocks are not supported; plain strings only
      while (j < n && src[j] !== '"') {
        if (src[j] === '\n') throw new LexError('Unterminated string literal', line);
        if (src[j] === '\\') { const r = unescape(src, j); out += r.ch; j = r.next; } else out += src[j++];
      }
      i = j + 1;
      push('str', out);
      continue;
    }
    if (c === "'") {
      let j = i + 1, out;
      if (src[j] === '\\') { const r = unescape(src, j); out = r.ch; j = r.next; } else out = src[j++];
      if (src[j] !== "'") throw new LexError('Bad character literal', line);
      i = j + 1;
      push('chr', out);
      continue;
    }
    let matched = null;
    for (const op of OPS) if (src.startsWith(op, i)) { matched = op; break; }
    if (!matched) throw new LexError(`Unexpected character "${c}"`, line);
    // Java has no <=> and `->` is the lambda arrow; C++ `->*` is vanishingly rare
    push('op', matched);
    i += matched.length;
  }
  toks.push({ t: 'eof', v: '<eof>', line });
  return { toks, defines };
}

function unescape(src, j) {
  const e = src[j + 1];
  const map = { n: '\n', t: '\t', r: '\r', '0': '\0', '\\': '\\', "'": "'", '"': '"', a: '\x07', b: '\b', f: '\f', v: '\v' };
  if (e === 'x') { const m = /^[0-9a-fA-F]{1,2}/.exec(src.slice(j + 2)); return { ch: String.fromCharCode(parseInt(m[0], 16)), next: j + 2 + m[0].length }; }
  if (e === 'u') { return { ch: String.fromCharCode(parseInt(src.slice(j + 2, j + 6), 16)), next: j + 6 }; }
  if (e in map) return { ch: map[e], next: j + 2 };
  return { ch: e, next: j + 2 };
}
