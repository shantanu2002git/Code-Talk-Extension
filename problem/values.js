// Parses LeetCode-style literal values: [1,2,3], [["a","b"]], "text", 'c', null, true, 1.5, 1e9.
// Anything that isn't a clean literal throws, so the caller can say "cannot run reliably" instead of guessing.

export function parseValue(raw) {
  let s = raw.trim();
  if (!s) throw new Error('empty value');
  // LeetCode sometimes uses typographic quotes; normalise.
  s = s.replace(/[“”]/g, '"').replace(/[‘’]/g, "'");
  // single-quoted tokens → double-quoted JSON strings
  s = s.replace(/'((?:[^'\\]|\\.)*)'/g, (_, g) => JSON.stringify(g.replace(/\\'/g, "'")));
  // 10^9 style
  s = s.replace(/\b(\d+)\s*\^\s*(\d+)\b/g, (_, a, b) => String(Number(a) ** Number(b)));
  try {
    return JSON.parse(s);
  } catch {
    throw new Error(`"${raw.length > 40 ? raw.slice(0, 40) + '…' : raw}" is not a recognised literal`);
  }
}

export function deepEqual(a, b) {
  if (a === b) return true;
  if (typeof a === 'number' && typeof b === 'number') return Math.abs(a - b) < 1e-5 * Math.max(1, Math.abs(a), Math.abs(b));
  if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((x, i) => deepEqual(x, b[i]));
  if (a && b && typeof a === 'object' && typeof b === 'object') {
    const ka = Object.keys(a);
    return ka.length === Object.keys(b).length && ka.every((k) => deepEqual(a[k], b[k]));
  }
  return false;
}
