// Public entry: static complexity analysis of the code in the editor.
import { Analyzer } from './analyzer.js';
import { clikeToIR } from './from-clike.js';
import { buildReport } from './explain.js';
import { Und } from './util.js';

/**
 * lang: 'cpp' | 'java' | 'python'; entry: function name; ir: pre-built IR (python); ctx: {lineCount}
 * Returns {ok:true, report, analyzer, result} or {ok:false, reason, line, hint}.
 */
export function analyzeComplexity({ lang, code, entry, ir = null, ctx = {} }) {
  let irr = ir;
  try {
    if (!irr) {
      if (lang === 'python') return { ok: false, reason: 'the Python source could not be parsed for analysis' };
      irr = clikeToIR(lang, code);
    }
    if (irr.error) return { ok: false, reason: irr.error };
  } catch (err) {
    return { ok: false, reason: `the code could not be parsed for analysis (${err.message})` };
  }
  const an = new Analyzer(irr);
  try {
    const result = an.analyze(entry);
    const report = buildReport(an, result, ctx);
    return { ok: true, report, analyzer: an, result };
  } catch (err) {
    if (err instanceof Und) return { ok: false, reason: err.reason, line: err.line, hint: err.hint, assumptions: [...an.assumptions.keys()] };
    return { ok: false, reason: `internal analysis error: ${err.message}`, internal: true, stack: err.stack };
  }
}
export { Analyzer, clikeToIR };
