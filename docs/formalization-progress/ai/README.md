# Formalization assistant (AI-driven progress tracking)

A proposal to complement the deterministic Python tracker
(`../formalization_progress.py`) with an AI assistant that maps the paper's
elements to the Lean declarations that formalize them. The assistant is a Claude
skill at [`.claude/skills/formalization-assistant/`](../../../.claude/skills/formalization-assistant/SKILL.md);
this directory holds the files it reads and writes.

## How to use it

The skill is a project skill, so Claude Code discovers it automatically in any
session opened in this repository. Three ways to invoke it:

- **Slash command.** Type `/formalization-assistant`, optionally with an
  instruction: `/formalization-assistant refresh the map and flag any green
  that overstates`.
- **Natural language.** Ask for the work and the skill's description triggers
  it: "refresh the formalization progress", "does `riuSigma` really formalize
  Equation 9?", "which paper elements are still unformalized?", "extract a
  structured version of the paper".
- **From another agent** in the same repository, the same way.

The run walks the six phases below and stops at the two review gates for the
developer. It does not write a confirmed mapping, or a date, into the learning
store without confirmation.

For a quick, deterministic, CI-checkable refresh with no review, run the script
directly instead:

```bash
python3 docs/formalization-progress/formalization_progress.py
```

The skill lives on the `formalization-assistant` branch; it becomes available on
other branches once that is merged.

## Why an assistant beside the script

The Python tracker joins the two sides on a citation tag with a regex. That is
fast, reproducible, and gated in CI, and it stays here unchanged. It cannot read
the mathematics: it accepts an `O24 Theorem 5.1` citation as-is, so a
declaration that cites an element without actually formalizing it still counts,
and it applies one fixed set of heuristics.

The assistant reads the mathematics. It judges whether a cited declaration
formalizes the object the paper states (right object, right quantifiers, proof
complete), so it can report a fidelity mismatch the join marks green. It also
lifts two of the script's rigidities: extraction is not pinned to numbered
environments, so the developer can track any span of the paper (a prose
definition, an algorithm, a security notion stated in text); and a mapping is
not pinned to a citation tag, so a declaration can be associated to an element by
a judged statement match or a reviewer's assertion, with the ground recorded. It
gives the developer control at each step through two review gates, and it records
every confirmed mapping and approved heuristic in `mappings.toml`, so it improves
as the project grows instead of re-deriving the same decisions.

The two coexist. Use the script for a quick, deterministic, CI-checkable
refresh. Use the assistant when you want to specify or document the mapping, or
want a fidelity read rather than a citation join. Both share one status
vocabulary, so their outputs are comparable.

## Workflow

The skill runs six phases with two human review gates.

1. Extract the paper into `paper-structure.toml` (numbered environments, curated
   figures and sections, each with section and page).
2. **Review gate.** The developer approves or edits the structure.
3. Draft one-line summaries per element in the domain's terminology, reusing
   `element_summaries.toml`.
4. **Review gate.** The developer owns the wording.
5. Map Lean declarations to paper elements: reuse confirmed mappings from
   `mappings.toml`, scan the sources, apply the approved heuristics, read the
   mathematics for fidelity, and record confirmed mappings back to
   `mappings.toml`.
6. Render `FORMALIZATION_PROGRESS.md`, or a richer GitHub view (issue task list,
   milestone, or Projects board) on request.

## Files

| File | Role |
|---|---|
| `mappings.toml` | learning store: confirmed mappings, approved heuristics, open questions. Versioned; edited by hand and appended to on confirmation. |
| `paper-structure.toml` | structured paper extraction (phase 1). Generated. |
| `README.md` | this file. |

The assistant reuses `../element_summaries.toml` and seeds phase 1 from
`../formalization_progress.json` when they exist.

## The learning store

`mappings.toml` is what makes the assistant get smarter. It holds:

- **Confirmed mappings**: paper element, Lean declarations, status, and the
  reviewer's rationale. Reused on the next run instead of re-derived.
- **Heuristics**: rules a reviewer approved for deciding a mapping (the
  citation-tag join, kind matching, assumption-versus-theorem, sorry demotion,
  and so on). The assistant applies them and names the one it used.
- **Open questions**: cases a reviewer flagged but did not settle, surfaced at
  the review gates rather than guessed.

It is seeded from the mappings the Python tracker currently reports, so the
assistant starts where the project already is.

## Status vocabulary

Identical to the Python tracker:

| Mark | Meaning |
|---|---|
| 🟢 | a sorry-free Lean declaration of the matching kind is cited |
| 🌐 | a matching declaration is cited but its body contains sorry/admit |
| 🌀 | a declaration is cited but its kind does not match the paper object |
| 🟡 | only module-level coverage |
| ⚪ | nothing yet |

Every 🟢 is a claim to verify, not a proof.
