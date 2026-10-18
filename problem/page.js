// Turns what the page extractor returned into a problem model: language, examples, entry-argument mapping.
import { extractExamples, splitAssignments } from './readme.js';
import { parseValue } from './values.js';

export function normLang(label, code = '') {
  const s = String(label || '').toLowerCase();
  if (/c\+\+|cpp|^c$/.test(s)) return 'cpp';
  if (/java(?!script)/.test(s)) return 'java';
  if (/python|py3|pypy/.test(s)) return 'python';
  if (/javascript|typescript|^js$|^ts$/.test(s)) return 'javascript';
  return guessLang(code);
}

export function guessLang(code) {
  const c = String(code || '');
  if (/#include|std::|vector<|->|\bcout\b|\bnullptr\b|class\s+Solution\s*\{\s*public:/.test(c)) return 'cpp';
  if (/\bpublic\s+(static\s+)?\w[\w<>\[\], ]*\s+\w+\s*\(|\bimport\s+java\.|\bSystem\.out\b|\bnew\s+\w+\[/.test(c)) return 'java';
  if (/^\s*def\s+\w+\s*\(|^\s*class\s+Solution\s*(\(.*\))?:|^\s*import\s+\w+|\bself\./m.test(c)) return 'python';
  if (/\bfunction\b|=>|\bconst\b|\blet\b/.test(c)) return 'javascript';
  return 'cpp';
}

/** GFG writes "arr[] = {1, 2, 3}" or "arr[] = 1 2 3" – bring it to "arr = [1, 2, 3]". */
export function normalizeGfgInput(s) {
  let t = s.replace(/\r/g, '');
  t = t.replace(/\b([A-Za-z_]\w*)\s*\[\s*\]\s*(\[\s*\])?\s*=/g, '$1 =');
  t = t.replace(/\{/g, '[').replace(/\}/g, ']');
  // "name = 1 2 3 4" (space separated numbers) -> list
  t = t.replace(/([A-Za-z_]\w*)\s*=\s*(-?\d+(?:\.\d+)?(?:\s+-?\d+(?:\.\d+)?)+)(?=\s*(?:,|\n|$|[A-Za-z_]\w*\s*=))/g, (m, n, v) => `${n} = [${v.trim().split(/\s+/).join(',')}]`);
  return t;
}

/** Examples found in the statement text. Each example: {inputs:[{name,raw,value}], expected, outputRaw, error} */
export function examplesFromText(text, site) {
  let t = String(text || '');
  if (site === 'gfg') {
    // GFG puts input/output on separate lines: "Input:\nN = 5\narr[] = ...\nOutput: ..."
    t = t.replace(/Input\s*:?\s*\n/gi, 'Input: ').replace(/\n\s*Output\s*:?\s*\n/gi, '\nOutput: ');
    t = normalizeGfgInput(t);
    t = t.replace(/Input:\s*([^\n]*)\n(?!\s*Output)([^\n]*=[^\n]*)\n/gi, (m, a, b) => `Input: ${a}, ${b}\n`);
  }
  let exs = extractExamples(t);
  if (site === 'gfg') {
    // line-wise fallback: join input lines with commas
    if (!exs.length || exs.every((e) => e.error)) {
      const re = /Input:?\s*\n?([\s\S]*?)\n\s*Output:?\s*\n?([^\n]*)/gi;
      let m; const out = [];
      while ((m = re.exec(t))) {
        const lines = m[1].split('\n').map((x) => x.trim()).filter(Boolean);
        const joined = lines.join(', ');
        const e2 = extractExamples(`Input: ${joined}\nOutput: ${m[2]}\n`);
        if (e2[0]) out.push(e2[0]);
      }
      if (out.length) exs = out;
    }
  }
  return exs;
}

export function parseInputText(text) {
  const assigns = splitAssignments(String(text || '').trim().replace(/\n+/g, ', ').replace(/,\s*,/g, ','));
  if (!assigns) return { error: 'Input must look like: nums = [1,2,3], target = 9' };
  try { return { inputs: assigns.map((a) => ({ name: a.name, raw: a.raw, value: parseValue(a.raw) })) }; } catch (e) { return { error: e.message }; }
}

/** Map example inputs to the entry function's parameters: by name first, otherwise by order. */
export function mapArgs(inputs, params) {
  if (!params || !params.length) return { args: inputs.map((i) => i.value), note: '' };
  const byName = params.map((p) => inputs.find((i) => i.name.toLowerCase() === p.name.toLowerCase()));
  if (byName.every(Boolean) && new Set(byName).size === params.length) return { args: byName.map((i) => i.value), note: '' };
  if (inputs.length === params.length) return { args: inputs.map((i) => i.value), note: 'Inputs were matched to the parameters by order.' };
  if (inputs.length > params.length) {
    // GFG often passes sizes ("n") that the parameter list does not have, or the other way round
    const sizeLike = inputs.filter((i) => /^(n|m|size|len|length|k_?size)$/i.test(i.name) && Number.isInteger(i.value) && inputs.some((o) => Array.isArray(o.value) && o.value.length === i.value));
    const rest = inputs.filter((i) => !sizeLike.includes(i));
    if (rest.length === params.length) return { args: rest.map((i) => i.value), note: `Dropped size argument(s) ${sizeLike.map((s) => s.name).join(', ')} that the function does not take.` };
  }
  if (inputs.length < params.length) {
    const arrLens = inputs.filter((i) => Array.isArray(i.value)).map((i) => i.value.length);
    const extraParams = params.length - inputs.length;
    const sizeParams = params.filter((p) => /^(n|m|size|len|length)$/i.test(p.name));
    if (sizeParams.length >= extraParams && arrLens.length) {
      const args = []; let k = 0;
      for (const p of params) { if (/^(n|m|size|len|length)$/i.test(p.name) && k >= 0 && !inputs.find((i) => i.name.toLowerCase() === p.name.toLowerCase())) args.push(arrLens[0]); else args.push(inputs[k++]?.value); }
      if (args.every((a) => a !== undefined)) return { args, note: 'Filled a size parameter from the array length.' };
    }
  }
  return { args: null, note: `The function takes ${params.length} parameter(s) (${params.map((p) => p.name).join(', ')}) but the input has ${inputs.length} value(s) (${inputs.map((i) => i.name).join(', ')}). Edit the Input box.` };
}

export function sameOutput(got, exp) {
  const eq = (a, b) => {
    if (a === b) return true;
    if (typeof a === 'number' && typeof b === 'number') return Math.abs(a - b) < 1e-5 * Math.max(1, Math.abs(a), Math.abs(b));
    if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((x, i) => eq(x, b[i]));
    if (a && b && typeof a === 'object' && typeof b === 'object') { const ka = Object.keys(a); return ka.length === Object.keys(b).length && ka.every((k) => eq(a[k], b[k])); }
    if (typeof a === 'boolean' && typeof b === 'string') return String(a) === b.toLowerCase();
    if (typeof a === 'string' && typeof b === 'boolean') return a.toLowerCase() === String(b);
    return false;
  };
  if (eq(got, exp)) return 'exact';
  const srt = (x) => (Array.isArray(x) ? x.map(srt).sort((p, q) => (JSON.stringify(p) < JSON.stringify(q) ? -1 : 1)) : x);
  if (eq(srt(got), srt(exp))) return 'reordered';
  return 'different';
}

/** The "answer" of a run: the return value, or (for in-place problems that return nothing) the first argument after the call. */
export function outputOf(run, args) {
  if (!run || run.error) return undefined;
  if (run.result !== undefined && run.result !== null) return run.result;
  if (run.argsAfter && run.argsAfter.length && args && args.length) {
    if (run.result === undefined || JSON.stringify(run.argsAfter[0]) !== JSON.stringify(args[0])) return run.argsAfter[0];
  }
  return run.result === null ? null : undefined;
}
