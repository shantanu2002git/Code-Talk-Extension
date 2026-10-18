// Runs the tracer inside an already loaded Pyodide instance (works in Node tests and in the extension worker).
let installed = new WeakSet();

export async function runPythonOn(py, tracerSrc, opts) {
  if (!installed.has(py)) { py.runPython(tracerSrc); installed.add(py); }
  const fn = py.globals.get('run_trace');
  try {
    const json = fn(opts.code, JSON.stringify(opts.args || []), opts.entry || '', JSON.stringify({ maxSteps: opts.maxSteps || 3000, timeMs: opts.timeMs || 9000, maxEvents: opts.maxEvents || 4000000 }));
    return JSON.parse(json);
  } finally { fn.destroy(); }
}
