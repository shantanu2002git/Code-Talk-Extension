// Parses the LeetHub-style README.md (HTML) into a readable statement + runnable examples.
import { parseValue } from './values.js';

const ENTITIES = { nbsp: ' ', lt: '<', gt: '>', amp: '&', quot: '"', apos: "'", le: '≤', ge: '≥', ne: '≠', times: '×', minus: '−', hellip: '…', ndash: '–', mdash: '—', rarr: '→', larr: '←', middot: '·', laquo: '«', raquo: '»' };

export function decodeEntities(s) {
  return s.replace(/&(#x[0-9a-f]+|#\d+|[a-z]+);/gi, (m, g) => {
    if (g[0] === '#') {
      const cp = g[1].toLowerCase() === 'x' ? parseInt(g.slice(2), 16) : parseInt(g.slice(1), 10);
      return Number.isFinite(cp) ? String.fromCodePoint(cp) : m;
    }
    return ENTITIES[g.toLowerCase()] ?? m;
  });
}

export function htmlToText(html) {
  let s = html;
  s = s.replace(/<img\b[^>]*>/gi, '');
  s = s.replace(/<sup>\s*([^<]*)<\/sup>/gi, '^$1');
  s = s.replace(/<sub>\s*([^<]*)<\/sub>/gi, '_$1');
  s = s.replace(/<br\s*\/?>/gi, '\n');
  s = s.replace(/<\/(p|div|pre|h[1-6]|ul|ol|table|tr)>/gi, '\n');
  s = s.replace(/<li[^>]*>/gi, '\n- ');
  s = s.replace(/<hr\s*\/?>/gi, '\n');
  s = s.replace(/<[^>]+>/g, '');
  s = decodeEntities(s);
  s = s.replace(/[ \t ]+\n/g, '\n').replace(/\n{3,}/g, '\n\n');
  return s.trim();
}

/** Split "a = [1,2], b = 3, s = "x, y"" into [{name, raw}] respecting brackets and quotes. */
export function splitAssignments(text) {
  const out = [];
  let depth = 0;
  let quote = '';
  let start = 0;
  const pieces = [];
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (quote) {
      if (c === '\\') i++;
      else if (c === quote) quote = '';
    } else if (c === '"' || c === "'") quote = c;
    else if (c === '[' || c === '{' || c === '(') depth++;
    else if (c === ']' || c === '}' || c === ')') depth--;
    else if (c === ',' && depth === 0 && /^\s*[A-Za-z_]\w*\s*=/.test(text.slice(i + 1))) {
      pieces.push(text.slice(start, i));
      start = i + 1;
    }
  }
  pieces.push(text.slice(start));
  for (const p of pieces) {
    const m = /^\s*([A-Za-z_]\w*)\s*=\s*([\s\S]*?)\s*$/.exec(p);
    if (!m) return null; // not an assignment list, can't be run reliably
    out.push({ name: m[1], raw: m[2] });
  }
  return out;
}

/** Extract "Input: ... Output: ..." examples from plain text (works for README and user descriptions). */
export function extractExamples(text) {
  const examples = [];
  const re = /Input:\s*([\s\S]*?)\n?\s*Output:\s*([\s\S]*?)(?=\n\s*(?:Explanation:|Example\s*\d*:?|Constraints:|Input:)|\n\s*\n|$)/gi;
  let m;
  while ((m = re.exec(text))) {
    const inputText = m[1].replace(/\s*\n\s*/g, ' ').trim();
    const outputRaw = m[2].replace(/\s*\n\s*/g, ' ').trim();
    const assigns = splitAssignments(inputText);
    const ex = { inputText, outputRaw, inputs: null, expected: undefined, error: null };
    if (!assigns) {
      ex.error = 'Input is not in "name = value, ..." form.';
    } else {
      try {
        ex.inputs = assigns.map((a) => ({ name: a.name, raw: a.raw, value: parseValue(a.raw) }));
      } catch (e) {
        ex.error = `Could not parse input value: ${e.message}`;
      }
    }
    try {
      ex.expected = parseValue(outputRaw);
    } catch {
      ex.expected = undefined; // free-text output, keep outputRaw for display only
    }
    examples.push(ex);
  }
  return examples;
}

export function parseReadme(html) {
  const out = { title: null, number: null, url: null, difficulty: null, statement: '', examples: [], constraints: [] };
  const h = /<h2>\s*<a\s+href="([^"]+)"[^>]*>\s*(?:(\d+)\.\s*)?([^<]+?)\s*<\/a>\s*<\/h2>/i.exec(html);
  if (h) {
    out.url = h[1];
    out.number = h[2] ? Number(h[2]) : null;
    out.title = decodeEntities(h[3]).trim();
  }
  // Two header layouts exist in the repo: "<h3>Easy</h3>" and a shields.io badge "Difficulty-Medium".
  const d1 = /<h3>\s*(Easy|Medium|Hard)\s*<\/h3>/i.exec(html);
  const d2 = /Difficulty-(Easy|Medium|Hard)/i.exec(html);
  const d = d1 || d2;
  if (d) out.difficulty = d[1][0].toUpperCase() + d[1].slice(1).toLowerCase();
  const body = html.replace(/<h2>[\s\S]*?<\/h2>/i, '').replace(/<h3>\s*(Easy|Medium|Hard)\s*<\/h3>/i, '');
  out.statement = htmlToText(body);
  out.examples = extractExamples(out.statement);
  const c = /Constraints:\s*([\s\S]*)$/i.exec(out.statement);
  if (c) out.constraints = c[1].split('\n').map((l) => l.replace(/^-\s*/, '').trim()).filter(Boolean);
  return out;
}
