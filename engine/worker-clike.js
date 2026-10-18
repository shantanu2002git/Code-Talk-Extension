// Web Worker: runs the C++ / Java tracing interpreter off the UI thread.
import { runClike } from './clike/run.js';
self.onmessage = (e) => {
  let out;
  try { out = runClike(e.data); } catch (err) { out = { ok: false, steps: [], error: { type: 'InternalError', message: String(err && err.message), kind: 'internal' } }; }
  delete out.value;
  self.postMessage(out);
};
