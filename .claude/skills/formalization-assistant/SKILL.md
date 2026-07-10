---
name: formalization-assistant
description: Track how far the Lean formalization has progressed against the source paper (Orrù, IACR 2024/1552). Use when asked to build, refresh, or review the formalization-progress map, to map a Lean declaration to a paper element, or to check paper-to-Lean fidelity. An AI-driven, review-gated alternative to docs/formalization-progress/formalization_progress.py that lets the developer specify and document each step, and that accumulates confirmed mappings in a learning store.
---

# Formalization assistant

An AI assistant that maps the elements of the source paper (Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552,
cited as `O24` in the Lean sources) to the Lean declarations that formalize
them, and renders a progress map. It answers, per paper
definition/lemma/theorem (and curated figures/sections/equations): is this
formalized in Lean yet, by which declaration, and does the proof look complete?

It is the AI-driven counterpart of the deterministic Python tracker at
`docs/formalization-progress/formalization_progress.py`. Both coexist. The
Python tool is fast, reproducible, and CI-gated; this assistant is slower but
reads the mathematics, so it can judge fidelity the regex join cannot, and it
records what a reviewer confirms so later runs improve. Treat every mapping it
proposes as a claim for a human to confirm, never as a verified fact.

## When to use

- "Refresh the formalization progress" / "rebuild the map".
- "Does this Lean declaration really formalize <paper element>?"
- "Which paper elements are still unformalized?"
- "Extract a structured version of the paper" / "summarize the paper elements".

For a quick, deterministic refresh with no review, run the Python tracker
instead (`python3 docs/formalization-progress/formalization_progress.py`). Use
this assistant when the developer wants to specify or document the mapping, or
wants a fidelity read rather than a citation join.

## Artifacts

Working directory is `docs/formalization-progress/ai/`.

| File | Role |
|---|---|
| `mappings.toml` | the learning store: confirmed paper ↔ Lean mappings, approved heuristics, open questions. Read it first; write to it only on confirmation. |
| `paper-structure.toml` | structured extraction of the paper (phase 1 output). |
| `element_summaries.toml` | curated one-line summaries. Reuse `../element_summaries.toml` if present. |
| `FORMALIZATION_PROGRESS.md` | rendered map (phase 6 output). Keep the Python tool's `../FORMALIZATION_PROGRESS.md` as the canonical committed copy unless told otherwise. |

The status vocabulary is identical to the Python tool, so the two never
disagree by convention: 🟢 sorry-free declaration of matching kind cited · 🌐
matching declaration cited but contains sorry/admit · 🌀 cited but kind
mismatches the paper object · 🟡 module-level coverage only · ⚪ nothing yet.

## Workflow

Six phases with two human review gates. Do not skip a gate. At each gate,
present the artifact, state what is uncertain, and wait for the developer to
approve or edit before continuing.

### Phase 1 — Extract the paper into a structured form

Extract whatever content the developer wants to track, not a fixed taxonomy.
Numbered environments (Theorem, Lemma, Definition, Claim, Corollary), figure
captions, and section headings are the default rows, but the developer may also
track any span the paper does not number: a prose definition, an algorithm or
protocol step, a security notion stated in text, an equation, an assumption
mentioned in passing. Give each element a free-form `kind` and a stable `key`;
record `section, section_title, page, statement` and, for an unnumbered span, a
short quote or anchor so a reviewer can find it. Delegate the extraction to a
subagent (the PDF is large). Seed from `../formalization_progress.json` (the
`paper` array) when it exists rather than re-extracting from scratch, then let
the developer add elements it missed. Write `paper-structure.toml`.

### Phase 2 — Review gate (paper structure)

Show the developer the element list and the count by kind. Flag anything the
extraction is unsure of (a split environment, an unnumbered claim, a figure
whose object is ambiguous). Apply their edits to `paper-structure.toml`.

### Phase 3 — Extract summaries for the paper elements

For each element, write a one-line summary in the domain's exact terminology.
Reuse existing entries in `element_summaries.toml` verbatim; only draft
summaries for elements that lack one. Default inclusion: numbered environments
always get a row; figures, sections, and equations get one when they carry a
formalizable object (a security game, a construction, a hardness assumption, a
proof-system interface), and equations are cite-driven. This is a default, not a
limit: summarize any span the developer chose to track in phase 1.

### Phase 4 — Review gate (summaries)

Show the new or changed summaries. The developer owns the wording; apply their
edits. Do not proceed with a summary they have not accepted.

### Phase 5 — Map Lean declarations to paper elements

1. Read `mappings.toml` and reuse every confirmed mapping and open question.
2. Scan every `*.lean` under `lean_root` (minus git-ignored paths and
   `exclude_dirs`) for declarations, in the docstring, signature, and module
   doc. Delegate a broad scan to a subagent. Collect both the `O24 <Element>`
   citations and, when the developer asks for a fidelity sweep, declarations
   whose statement matches a paper element even without a tag.
3. Associate declarations to elements by the strongest available evidence, and
   record which it was: an `O24 <Element>` citation (strongest), a statement the
   assistant judges to match a paper element (proposed, needs confirmation), or
   a mapping the developer asserts directly. A citation is not required; a
   reviewer-asserted mapping is valid and recorded as `evidence = "asserted"`.
4. Apply the approved heuristics in `mappings.toml` (`[[heuristic]]`) in order,
   and assign a status. State which heuristic decided each non-obvious case.
5. Read the mathematics, not only the citation. Judge whether the declaration
   actually formalizes the element (right object, right quantifiers, no sorry on
   the transitive proof). This fidelity read is what distinguishes the assistant
   from the regex join; report a mismatch as a finding, not a silent 🟢.
6. Present new or changed mappings to the developer. On confirmation, append
   them to `mappings.toml` with `evidence`, `confirmed_by`, `confirmed_on`, and
   a `rationale`. This is how the assistant gets smarter: a confirmed mapping is
   reused next time instead of re-derived, and any new rule the reviewer states
   becomes a `[[heuristic]]`.

Never invent a date. Ask the developer for the confirmation date, or read it
from `git log`, before writing `confirmed_on`.

### Phase 6 — Present the result

Render `FORMALIZATION_PROGRESS.md`: a header noting it is an approximate,
review-gated map (not an authoritative measurement); summary counts by paper
element kind and by Lean declaration kind; the status legend; and the
element → declarations table with each element linked to its PDF page. Match the
Python tool's table shape so the two outputs are comparable.

Step 6 has a growth path the developer chooses per run:

- **Simple**: the Markdown table above.
- **Richer**: a GitHub view. Options, in increasing effort: a task list in an
  issue, one issue per unformalized element grouped in a milestone, or a GitHub
  Projects board with a status field driven from `mappings.toml`. Propose the
  level; build it with `gh` only when the developer asks.

## Guardrails

- Every 🟢 is a claim to verify, never a proof. Say so in the output header.
- Do not edit generated files by hand as if authored; regenerate them.
- A citation tag is the strongest evidence but not a requirement. A mapping may
  rest on a statement match or a reviewer's assertion; always record which in
  `evidence`, so the ground for each mapping stays auditable. An `O24 <Element>`
  citation keeps the Python tool and this assistant in agreement, so prefer
  adding the tag to the Lean source when a mapping is confirmed by other means.
- Keep the status vocabulary identical to the Python tool. The inclusion rule is
  a default, not a limit: the developer may track content the Python tool omits.
- Follow the repository style guide (`docs/STYLE_GUIDE.md`) for all prose and
  math notation.
