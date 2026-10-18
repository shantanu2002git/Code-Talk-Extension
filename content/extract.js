// Injected into the page's MAIN world on demand (chrome.scripting.executeScript). Defines window.__codeTalkExtract().
// It reads the problem title / statement from the DOM and the code from the page's editor object (Monaco on LeetCode,
// Ace / CodeMirror on GeeksforGeeks), falling back to the visible editor text. Nothing is sent anywhere.
(function () {
  const pick = (sels, root = document) => { for (const s of sels) { try { const el = root.querySelector(s); if (el && (el.innerText || el.textContent || '').trim()) return el; } catch (e) { /* invalid selector */ } } return null; };
  const text = (el) => (el ? (el.innerText || el.textContent || '').replace(/ /g, ' ').trim() : '');

  function monacoCode() {
    const m = window.monaco && window.monaco.editor;
    if (!m) return null;
    let model = null;
    try {
      const eds = m.getEditors ? m.getEditors() : [];
      const focused = eds.find((e) => e.hasTextFocus && e.hasTextFocus()) || eds.find((e) => e.getModel && e.getModel() && e.getModel().getLanguageId() !== 'plaintext') || eds[0];
      if (focused && focused.getModel) model = focused.getModel();
    } catch (e) { /* ignore */ }
    if (!model) {
      const models = m.getModels ? m.getModels() : [];
      model = models.slice().sort((a, b) => b.getValueLength() - a.getValueLength())[0] || null;
    }
    if (!model) return null;
    return { code: model.getValue(), language: model.getLanguageId ? model.getLanguageId() : (model.getModeId ? model.getModeId() : ''), source: 'monaco' };
  }
  function aceCode() {
    const els = document.querySelectorAll('.ace_editor');
    for (const el of els) {
      const ed = el.env && el.env.editor;
      if (ed && ed.getValue) {
        const v = ed.getValue();
        let lang = '';
        try { lang = (ed.session.getMode().$id || '').split('/').pop(); } catch (e) { /* ignore */ }
        if (v && v.trim()) return { code: v, language: lang, source: 'ace' };
      }
    }
    return null;
  }
  function codeMirrorCode() {
    const el = document.querySelector('.CodeMirror');
    if (el && el.CodeMirror) return { code: el.CodeMirror.getValue(), language: el.CodeMirror.getOption('mode') || '', source: 'codemirror' };
    const cm6 = document.querySelector('.cm-content');
    if (cm6) { const lines = [...cm6.querySelectorAll('.cm-line')].map((l) => l.textContent); if (lines.length) return { code: lines.join('\n'), language: '', source: 'codemirror6' }; }
    return null;
  }
  function visibleCode() {
    const vl = document.querySelector('.monaco-editor .view-lines');
    if (vl) { const lines = [...vl.querySelectorAll('.view-line')].sort((a, b) => parseFloat(a.style.top) - parseFloat(b.style.top)).map((l) => l.textContent.replace(/ /g, ' ')); if (lines.length) return { code: lines.join('\n'), language: '', source: 'visible-lines', partial: true }; }
    const ta = [...document.querySelectorAll('textarea')].sort((a, b) => b.value.length - a.value.length)[0];
    if (ta && ta.value.trim().length > 20) return { code: ta.value, language: '', source: 'textarea' };
    return null;
  }

  function leetcodeLanguageLabel() {
    const btn = document.querySelector('button[id^="headlessui-popover-button"], [data-cy="lang-select"], button[aria-haspopup="dialog"]');
    return btn ? text(btn) : '';
  }
  function gfgLanguageLabel() {
    const el = pick(['[class*="language"] [class*="select"]', '[class*="ProblemLang"]', '.language-select', 'select']);
    if (!el) return '';
    return el.tagName === 'SELECT' ? el.options[el.selectedIndex].text : text(el);
  }

  function extract() {
    const host = location.hostname;
    const out = { ok: true, url: location.href, host, site: /leetcode/.test(host) ? 'leetcode' : /geeksforgeeks/.test(host) ? 'gfg' : 'other', title: '', slug: '', number: null, description: '', code: '', language: '', languageLabel: '', editor: '', partialCode: false, notes: [] };
    const path = location.pathname;
    const sm = /\/problems\/([^/]+)/.exec(path);
    if (sm) out.slug = sm[1];

    if (out.site === 'leetcode') {
      const t = pick(['[data-cy="question-title"]', 'div[class*="text-title-large"] a', 'a[href^="/problems/"][class*="text-title"]', '.css-v3d350', 'h4 a[href^="/problems/"]', 'div[data-track-load="qd_title"]']);
      out.title = text(t) || document.title.replace(/\s*-\s*LeetCode.*$/i, '').trim();
      const d = pick(['[data-track-load="description_content"]', 'div[class*="elfjS"]', '.content__u3I1', 'div[class*="question-content"]', '[class*="description__"] [class*="content"]', 'meta[name="description"]']);
      out.description = d && d.tagName === 'META' ? d.content : text(d);
      if (!out.description) { const og = document.querySelector('meta[property="og:description"]'); if (og) out.description = og.content; }
      out.languageLabel = leetcodeLanguageLabel();
    } else if (out.site === 'gfg') {
      const t = pick(['[class*="problems_header_content__title"] h3', '[class*="problems_header_content__title"]', '.problem-tab h3', 'h3', 'h1']);
      out.title = text(t) || document.title.replace(/\s*\|.*$/, '').trim();
      const d = pick(['[class*="problems_problem_content"]', '.problem-statement', '[class*="problem-statement"]', '.problems_problem_content__Xm_eO', 'article', 'main']);
      out.description = text(d);
      out.languageLabel = gfgLanguageLabel();
    } else {
      out.title = document.title;
    }
    const nm = /^\s*(\d+)\.\s*(.+)$/.exec(out.title);
    if (nm) { out.number = Number(nm[1]); out.title = nm[2].trim(); }

    const c = monacoCode() || aceCode() || codeMirrorCode() || visibleCode();
    if (c) { out.code = c.code; out.language = c.language || ''; out.editor = c.source; out.partialCode = Boolean(c.partial); if (c.partial) out.notes.push('Only the visible editor lines could be read; scroll the editor to the top or paste the code manually.'); }
    else out.notes.push('No code editor was found on this page. Paste your code into the Code box.');
    return out;
  }

  window.__codeTalkExtract = function () { try { return extract(); } catch (e) { return { ok: false, error: String(e && e.message || e) }; } };
})();
