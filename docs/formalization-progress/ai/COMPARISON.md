# AI map vs. Python tracker

A run of the `formalization-assistant` skill against the same sources the Python
tracker uses (`../formalization_progress.py`), on branch `formalization-assistant`
at the current HEAD. Both read O24 and the `KVAC/` Lean tree; the comparison
isolates what reading the mathematics adds to the citation join.

## Where they agree

- **Same catalogue**: 56 paper elements, identical keys, sections, and pages
  (the AI run seeds phase 1 from the tracker's `paper` array).
- **Same marks on all 8 associated elements**: 6 🟢 and 2 🌀. No element gets a
  different status symbol.
- **Same 🌀 diagnosis**: `threeDlogAdv` / `twoDlogAdv` cite Theorem 5.1 / 5.3 but
  are the assumptions those theorems use, not proofs of them. Both tools mark
  🌀; the assistant reaches it through the `assumption-vs-theorem` heuristic in
  the learning store rather than by kind comparison alone.
- **Same top-line coverage**: ~6/56 (~11%).

So on the numbers a reviewer would report, the two tools do not disagree. This is
by design: the assistant keeps the Python tool's status vocabulary.

## Where they differ

The regex join accepts an `O24 <Element>` citation and checks only that a
declaration of the matching *kind* exists. It cannot see whether the declaration
formalizes the object the paper states. The assistant reads the cited code and
adds a **fidelity** column. Of the 6 greens, it rates 3 high and 3 partial.

| Element | Both | AI fidelity | What the join misses |
|---|:--:|:--:|---|
| Definition 3.1 | 🟢 | high | — |
| Figure 5 | 🟢 | high | — |
| Equation 9 | 🟢 | high | If anything under-credited: one row hides a full Σ-protocol with sorry-free completeness, special soundness, and HVZK. |
| §3.1 | 🟢 | **partial** | q-DL and gap-DL are formalized; the q-DDHI assumption the section also states is deferred. |
| §3.3 | 🟢 | **partial** | The green rests on the *agnostic* NIZKP spec (`NIZKP/Basic.lean`). It formalizes the property shape (`SimulationExtractable`, `ZeroKnowledge`, `KnowledgeSound`) but abstracts the computational content: `indist` relates a single pair of outputs, not a negligible advantage; `extracts` is a model-supplied relation, not the paper's extractor over the prover's coins and code. The quantitative §3.3 notion lives in a refinement that is not on this branch. |
| Figure 9 | 🟢 | **partial** | Only the Base MAC `(S,K,M,V)` with correctness and the `R_iu` Σ-protocol are formalized. Issue/Present and the relations `R_is`/`R_p` (Eqs. 10-11) are out of scope, per the module doc. The full construction is not covered. |

## Reading

The green count is the same, but the assistant reports that half the greens
formalize a slice or a shape rather than the whole object. An honest coverage
statement is therefore weaker than "6 done": three are complete
(Definition 3.1, Figure 5, Equation 9) and three are partial (§3.1, §3.3,
Figure 9). The §3.3 case is the sharpest, because a citation-only tool cannot
tell that the cited spec deliberately abstracts away the security content it is
supposed to certify.

The cost is the opposite trade: the assistant is slower, non-reproducible run to
run, and its fidelity reads are themselves claims to verify, whereas the Python
`--check` gate is deterministic and cheap. The intended use is both, the script
in CI for drift, the assistant when a reviewer wants to know whether a green is
real.

## Artifacts

- AI map: `FORMALIZATION_PROGRESS.md` (this directory).
- Python map: `../FORMALIZATION_PROGRESS.md`.
- Learning store seeded from this run: `mappings.toml`.
