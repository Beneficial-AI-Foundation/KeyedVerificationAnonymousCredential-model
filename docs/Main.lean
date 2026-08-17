import VersoManual
import VersoBlueprint
import KVACDocs.Contents

open Verso.Genre Manual
open Informal

def bpCss : CSS := CSS.mk
r#"
/* Lean syntax highlighting colors (github-light theme) */
:root {
  --verso-code-keyword-color: #D73A49;
  --verso-code-keyword-weight: normal;
}
.hl.lean .keyword { color: #D73A49; }
.hl.lean .var { color: #24292E; }
.hl.lean .const { color: #6F42C1; }
.hl.lean .sort { color: #005CC5; }
.hl.lean .literal { color: #005CC5; }
.hl.lean .string { color: #032F62; }
.hl.lean .unknown { color: #24292E; }
.hl.lean .inter-text { color: #24292E; }

/* Rendered docstrings inside code blocks */
.bp_external_decl_body .docstring {
  font-family: var(--verso-text-font-family, sans-serif);
  font-size: 0.95em;
  line-height: 1.5;
  white-space: normal;
  padding: 0.6rem 0.8rem;
  margin: 0.4rem 0 0 0;
  background: #f8fafc;
  border-left: 3px solid #6F42C1;
  border-radius: 0 4px 4px 0;
}
.bp_external_decl_body .docstring code {
  background: #eef2f7;
  padding: 0.1em 0.3em;
  border-radius: 3px;
  font-size: 0.9em;
}
.bp_external_decl_body .docstring p {
  margin: 0.3em 0;
}

/* Proof source card — no purple left border */
.proof-source-card {
  margin: 0.8rem 0;
  border: none;
  border-left: none;
  background: transparent;
  overflow: hidden;
}
.proof-source-card.bp_code_panel {
  border-left: none !important;
}
.proof-source-code {
  margin: 0;
  padding: 0.8rem 1rem;
  font-family: monospace;
  font-size: 0.88em;
  line-height: 1.6;
  white-space: pre;
  overflow-x: auto;
  color: #24292E;
  background: var(--bp-color-surface-muted, #f8fafc);
  border-left: 3px solid #6F42C1;
  border-radius: 0 4px 4px 0;
}


/* Hide "Code for ..." cards — L∃∀N links already show declarations */
.bp_code_panel_wrapper {
  display: none !important;
}

/* Blueprint heading: "Definition 1.1 (name)" pattern */
.bp_name {
  font-weight: bold;
  font-style: italic;
  white-space: nowrap;
}
.bp_heading_title_row_statement {
  display: inline-flex !important;
  align-items: baseline;
  gap: 0.35rem;
  white-space: nowrap;
}

/* Home icon in the header logo slot, linking back to the landing page. */
.kvac-home-link {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  padding: 0.45rem;
  border-radius: 0.4rem;
  color: inherit;
}
.kvac-home-link:hover {
  background: rgba(0, 0, 0, 0.07);
}

/* Landing-page design language, applied site-wide. Token values mirror the
   dashboard CSS in scripts/blueprint_dashboard.py; keep the two in step. */
:root {
  --kvac-fg: #1f2937;
  --kvac-muted: #6b7280;
  --kvac-line: #e5e7eb;
  --kvac-accent: #0f766e;

  /* Verso chrome */
  --verso-text-font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
  --verso-structure-font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
  --verso-text-color: var(--kvac-fg);
  --verso-structure-color: var(--kvac-fg);
  --verso-toc-background-color: #f9fafb;

  /* Blueprint cards: neutral hairlines, teal accent, flat landing-page geometry */
  --bp-color-link: var(--kvac-accent);
  --bp-color-text: var(--kvac-fg);
  --bp-color-modern-border: var(--kvac-line);
  --bp-color-surface-modern: #ffffff;
  --bp-color-modern-surface-alt: #f9fafb;
  --bp-color-modern-caption: #f3f4f6;
  --bp-radius-2xl: 0.6rem;
  --bp-shadow-modern: none;
}

body { color: var(--kvac-fg); }
.header-title { color: var(--kvac-fg); }
#toc a { color: var(--kvac-fg); }
#toc a:hover { color: var(--kvac-accent); }
main a { color: var(--kvac-accent); }

/* Element-kind filter bar (populated by bpJs on pages with blueprint nodes) */
.kvac-filterbar {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.5rem;
  margin: 1rem 0 1.2rem;
}
.kvac-filterbar-label {
  color: var(--kvac-muted);
  font-size: 0.85rem;
}
.kvac-chip {
  border: 1px solid var(--kvac-line);
  border-radius: 999px;
  padding: 0.15rem 0.75rem;
  font: inherit;
  font-size: 0.85rem;
  background: #ffffff;
  color: var(--kvac-fg);
  cursor: pointer;
}
.kvac-chip:hover {
  border-color: var(--kvac-accent);
}
.kvac-chip[aria-pressed="true"] {
  background: var(--kvac-accent);
  border-color: var(--kvac-accent);
  color: #ffffff;
}
"#

def bpJs : JS := JS.mk
r#"
(function() {
  function onReady(fn) {
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', fn);
    } else {
      fn();
    }
  }

  /* Insert blueprint label names: "Definition 1.1" -> "Definition 1.1 (dh_spec)" */
  onReady(function() {
    document.querySelectorAll('.bp_heading_title_row_statement').forEach(function(row) {
      if (row.querySelector('.bp_name')) return;
      var caption = row.querySelector('.bp_caption[title]');
      if (!caption) return;
      var name = caption.getAttribute('title');
      if (!name || name.length === 0) return;
      var nameSpan = document.createElement('span');
      nameSpan.className = 'bp_name';
      nameSpan.textContent = '(' + name + ')';
      row.appendChild(nameSpan);
    });
  });

  /* Render markdown in docstrings */
  onReady(function() {
    if (typeof marked !== 'undefined') {
      document.querySelectorAll('pre.docstring, code.docstring').forEach(function(el) {
        if (el.dataset.rendered) return;
        /* Skip docstrings inside hover-info (those are Mathlib tooltips) */
        if (el.closest('.hover-info')) return;
        el.dataset.rendered = '1';
        var text = el.innerText;
        if (!text || !text.trim()) return;
        var html = marked.parse(text);
        var rendered = document.createElement('div');
        rendered.className = 'docstring';
        rendered.innerHTML = html;
        el.parentNode.replaceChild(rendered, el);
      });
    }
  });

  /* Set modern style by default */
  onReady(function() {
    document.documentElement.setAttribute('data-bp-style', 'modern');
  });

  /* Suppress empty Tippy tooltips */
  onReady(function() {
    document.querySelectorAll('.hover-info').forEach(function(el) {
      var text = el.textContent.trim();
      if (!text) el.remove();
    });
  });

  /* Landing-page link: fill the (empty) header logo slot with a home icon
     pointing at the site root, one level above html-multi/. Works at any
     page depth by stripping the html-multi/... suffix from the path. */
  onReady(function() {
    var slot = document.querySelector('header .header-logo-wrapper');
    if (!slot || slot.querySelector('.kvac-home-link')) return;
    var root = location.pathname.replace(/html-multi\/.*$/, '');
    if (root === location.pathname) return;
    var link = document.createElement('a');
    link.className = 'kvac-home-link';
    link.href = root;
    link.title = 'Project landing page (progress dashboard)';
    link.setAttribute('aria-label', 'Project landing page');
    link.innerHTML =
      '<svg viewBox="0 0 24 24" width="22" height="22" fill="none" ' +
      'stroke="currentColor" stroke-width="2" stroke-linecap="round" ' +
      'stroke-linejoin="round" aria-hidden="true">' +
      '<path d="M3 10.5 12 3l9 7.5"/>' +
      '<path d="M5 9.5V21h5v-6h4v6h5V9.5"/></svg>';
    slot.appendChild(link);
  });

  /* Element-kind filter: chips that show/hide definition/theorem/proof
     blocks on the current page. Kinds are discovered from the standalone
     bp_kind_<kind> class on each .bp_wrapper; choices persist across pages
     via localStorage. Rendered only on pages that have blueprint nodes. */
  onReady(function() {
    var KNOWN = ['definition', 'theorem', 'lemma', 'proposition',
                 'corollary', 'example', 'remark', 'proof'];
    var LABELS = { definition: 'Definitions', theorem: 'Theorems',
                   lemma: 'Lemmas', proposition: 'Propositions',
                   corollary: 'Corollaries', example: 'Examples',
                   remark: 'Remarks', proof: 'Proofs' };
    var byKind = {};
    document.querySelectorAll('.bp_wrapper').forEach(function(el) {
      var m = el.className.match(/(?:^|\s)bp_kind_([a-z]+)(?:\s|$)/);
      if (!m) return;
      (byKind[m[1]] = byKind[m[1]] || []).push(el);
    });
    var kinds = Object.keys(byKind);
    if (kinds.length === 0) return;
    kinds.sort(function(a, b) {
      var ia = KNOWN.indexOf(a), ib = KNOWN.indexOf(b);
      if (ia < 0) ia = KNOWN.length;
      if (ib < 0) ib = KNOWN.length;
      return ia - ib || a.localeCompare(b);
    });

    var STORE_KEY = 'kvac-bp-kind-filters';
    var stored = {};
    try { stored = JSON.parse(localStorage.getItem(STORE_KEY) || '{}'); }
    catch (e) { stored = {}; }

    function apply(kind, shown) {
      byKind[kind].forEach(function(el) {
        el.style.display = shown ? '' : 'none';
      });
    }

    var bar = document.createElement('div');
    bar.className = 'kvac-filterbar';
    bar.setAttribute('role', 'group');
    bar.setAttribute('aria-label', 'Filter elements by kind');
    var label = document.createElement('span');
    label.className = 'kvac-filterbar-label';
    label.textContent = 'Show:';
    bar.appendChild(label);

    kinds.forEach(function(kind) {
      var shown = stored[kind] !== false;
      var chip = document.createElement('button');
      chip.type = 'button';
      chip.className = 'kvac-chip';
      chip.setAttribute('aria-pressed', String(shown));
      chip.textContent = (LABELS[kind] || kind) + ' (' + byKind[kind].length + ')';
      chip.addEventListener('click', function() {
        var nowShown = chip.getAttribute('aria-pressed') !== 'true';
        chip.setAttribute('aria-pressed', String(nowShown));
        stored[kind] = nowShown;
        try { localStorage.setItem(STORE_KEY, JSON.stringify(stored)); }
        catch (e) {}
        apply(kind, nowShown);
      });
      apply(kind, shown);
      bar.appendChild(chip);
    });

    var content = document.querySelector('main .content-wrapper') ||
                  document.querySelector('main');
    if (!content) return;
    var nav = content.querySelector(':scope > nav.prev-next-buttons');
    if (nav) nav.insertAdjacentElement('afterend', bar);
    else content.insertAdjacentElement('afterbegin', bar);
  });
})();
"#

def main (args : List String) : IO UInt32 :=
  PreviewManifest.blueprintMainWithPreviewData
    (%doc KVACDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := {
      toHtmlAssets := {
        extraCss := .ofList [bpCss]
        extraJs := .ofList [bpJs]
      }
    })
