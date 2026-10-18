// Web Worker: loads Pyodide (CPython compiled to WebAssembly, bundled with the extension) and runs the tracer.
import { loadPyodide } from '../vendor/pyodide/pyodide.mjs';
import { runPythonOn } from './python/run.js';
let pyP = null, tracer = null, irSrc = null;
async function boot() {
  const base = new URL('../vendor/pyodide/', import.meta.url).href;
  const py = await loadPyodide({ indexURL: base, lockFileURL: base + 'pyodide-lock.json' });
  tracer = await (await fetch(new URL('./python/tracer.py', import.meta.url))).text();
  return py;
}
self.onmessage = async (e) => {
  const msg = e.data;
  try {
    if (!pyP) { self.postMessage({ type: 'status', text: 'Loading Python runtime (first time only)…' }); pyP = boot(); }
    const py = await pyP;
    if (msg.type === 'warmup') { self.postMessage({ type: 'ready' }); return; }
    if (msg.type === 'ir') {
      if (!irSrc) { irSrc = await (await fetch(new URL('../complexity/python-ir.py', import.meta.url))).text(); py.runPython(irSrc); }
      const fn = py.globals.get('build_ir');
      try { self.postMessage({ type: 'ir-result', id: msg.id, json: fn(msg.code) }); } finally { fn.destroy(); }
      return;
    }
    const out = await runPythonOn(py, tracer, msg);
    self.postMessage({ type: 'result', out });
  } catch (err) {
    if (msg && msg.type === 'ir') { self.postMessage({ type: 'ir-result', id: msg.id, json: JSON.stringify({ error: String(err && err.message || err) }) }); return; }
    self.postMessage({ type: 'result', out: { ok: false, steps: [], error: { type: 'InternalError', message: String(err && err.message || err), kind: 'internal' } } });
  }
};
