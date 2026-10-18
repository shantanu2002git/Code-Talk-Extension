// Bundled correct solutions, looked up by problem slug / title (LeetCode slug, or GeeksforGeeks title).
let libP = null;
export function loadLibrary() {
  if (!libP) libP = fetch(new URL('./library.json', import.meta.url)).then((r) => r.json()).catch(() => ({ problems: {}, aliases: {} }));
  return libP;
}
const norm = (s) => String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim();

export async function findProblem({ slug, title }) {
  const lib = await loadLibrary();
  if (slug && lib.problems[slug]) return { slug, ...lib.problems[slug] };
  const byTitle = lib.aliases[norm(title)];
  if (byTitle) return { slug: byTitle, ...lib.problems[byTitle] };
  const s2 = norm(slug);
  if (s2 && lib.aliases[s2]) return { slug: lib.aliases[s2], ...lib.problems[lib.aliases[s2]] };
  return null;
}

/** Best reference code for `lang`; falls back to another language when no version of that language is bundled. */
export function pickReference(entry, lang) {
  if (!entry) return null;
  const order = [lang, 'cpp', 'java', 'python'].filter((v, i, a) => a.indexOf(v) === i);
  for (const l of order) if (entry.code[l]) return { lang: l, code: entry.code[l], exact: l === lang };
  return null;
}
