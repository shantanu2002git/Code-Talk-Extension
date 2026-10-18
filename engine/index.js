// Engine client used by the panel. Each language runs in a Web Worker that is killed if it exceeds the hard timeout.
const url = (p) => new URL(p, import.meta.url);

function runClikeWorker(opts, hardMs) {
  return new Promise((resolve) => {
    const w = new Worker(url('./worker-clike.js'), { type: 'module' });
    const timer = setTimeout(() => { w.terminate(); resolve({ ok: false, steps: [], error: { type: 'Limit', kind: 'limit', message: 'The program ran for too long and was stopped (possible infinite loop or very heavy computation).' } }); }, hardMs);
    w.onmessage = (e) => { clearTimeout(timer); w.terminate(); resolve(e.data); };
    w.onerror = (e) => { clearTimeout(timer); w.terminate(); resolve({ ok: false, steps: [], error: { type: 'InternalError', kind: 'internal', message: `Worker failed: ${e.message || 'unknown error'}` } }); };
    w.postMessage(opts);
  });
}

let pyWorker = null;
function pyStart(onStatus) {
  if (pyWorker) return pyWorker;
  pyWorker = new Worker(url('./worker-python.js'), { type: 'module' });
  pyWorker.addEventListener('message', (e) => { if (e.data && e.data.type === 'status' && onStatus) onStatus(e.data.text); });
  return pyWorker;
}
let pyQueue = Promise.resolve();
/** one job at a time: results carry no id, so concurrent jobs would receive each other's answers */
function runPythonWorker(opts, hardMs, onStatus) {
  const job = pyQueue.then(() => runPythonNow(opts, hardMs, onStatus));
  pyQueue = job.catch(() => {});
  return job;
}
function runPythonNow(opts, hardMs, onStatus) {
  return new Promise((resolve) => {
    const w = pyStart(onStatus);
    // first call also loads the runtime, which is slow: give it extra time before the hard stop
    const timer = setTimeout(() => { w.terminate(); pyWorker = null; resolve({ ok: false, steps: [], error: { type: 'Limit', kind: 'limit', message: 'The Python program ran for too long and was stopped.' } }); }, hardMs + (pyLoaded ? 0 : 45000));
    const onMsg = (e) => {
      if (!e.data || e.data.type !== 'result') return;
      clearTimeout(timer); w.removeEventListener('message', onMsg); pyLoaded = true; resolve(e.data.out);
    };
    w.addEventListener('message', onMsg);
    w.onerror = (e) => { clearTimeout(timer); try { w.terminate(); } catch {} pyWorker = null; resolve({ ok: false, steps: [], error: { type: 'InternalError', kind: 'internal', message: `Python worker failed: ${e.message || 'could not start (WebAssembly blocked?)'}` } }); };
    w.postMessage(opts);
  });
}
let pyLoaded = false;

export function warmupPython(onStatus) { try { pyStart(onStatus).postMessage({ type: 'warmup' }); } catch {} }

/** lang: 'cpp' | 'java' | 'python'. Returns the trace result object. */
export async function runTrace({ lang, code, args, entry, maxSteps = 3000, maxOps, maxEvents, onStatus }) {
  if (lang === 'python') return runPythonWorker({ type: 'run', code, args, entry, maxSteps, maxEvents, timeMs: 9000 }, 12000, onStatus);
  if (lang === 'cpp' || lang === 'java') return runClikeWorker({ lang, code, args, entry, maxSteps, maxOps, timeMs: 8000 }, 14000);
  return { ok: false, steps: [], error: { type: 'Unsupported', kind: 'unsupported', message: `Language "${lang}" cannot be traced yet. Pick C++, Java or Python.` } };
}

let irSeq = 0;
/** Python source -> complexity IR (runs python's own `ast` inside the Pyodide worker) */
export function pythonIR(code, onStatus) {
  return new Promise((resolve) => {
    const w = pyStart(onStatus);
    const id = ++irSeq;
    const timer = setTimeout(() => { w.removeEventListener('message', on); resolve({ error: 'The Python runtime did not answer in time.' }); }, pyLoaded ? 15000 : 60000);
    const on = (e) => { if (!e.data || e.data.type !== 'ir-result' || e.data.id !== id) return; clearTimeout(timer); w.removeEventListener('message', on); try { resolve(JSON.parse(e.data.json)); } catch { resolve({ error: 'bad IR' }); } };
    w.addEventListener('message', on);
    w.postMessage({ type: 'ir', code, id });
  });
}
