# Blueprint docs maintenance

How to keep the Verso blueprint docs (`docs/KVACDocs/`) in step with the Lean
sources. The published site renders a dependency graph and a progress summary
from the blueprint nodes; CI (`docs-ci.yml`) fails any PR whose docs drift
from the code. This guide is the playbook plus the conventions and decisions
behind them.

## Update playbook (a PR merged, now update the docs)

1. Rebuild the root library first, or stale `.olean`s will lie to step 2:
   `lake build`
2. Regenerate the declaration manifest:
   `lake env lean --run scripts/blueprint_decl_manifest.lean > /tmp/manifest.tsv`
3. For each new declaration, either extend an existing node's
   `(lean := "…")` list or add a node (see conventions). Paper elements come
   from `docs/formalization-progress/element_summaries.toml`; work that is not
   a paper element gets a `milestone` node.
4. Wire dependencies. Statement dependencies as `{uses "label"}[]` in the node
   body; proof dependencies inside the node's `:::proof` block. Prose links
   that must not create an edge use `{bpref "label"}[]`.
5. Build and check:
   `lake -d docs build KVACDocs`
   `python3 scripts/blueprint_coverage_check.py /tmp/manifest.tsv`
6. Preview locally:
   `cd docs && lake env lean --run Main.lean --output _out/site`
   (`docs/_out/` is gitignored; do not output to an unignored path.)

## Conventions

- **Anchoring honesty rule.** A paper-element node gets a `lean :=` anchor
  only when the bound declarations state that element in full. Partial results
  anchor their own `milestone` node instead, and the paper element depends on
  it via `uses`. Example: Lemma 5.4 stays unanchored while its identity case,
  AGM game, and sign-mask milestones are done.
- **One node per tracker element** (Definition/Theorem/Lemma/Claim/Corollary/
  Figure/Equation/§-interface), labels are descriptive snake_case
  (`credential_predicate`, not `def_4_1`); the paper number lives in
  `tags := "paper, O24 Def 4.1"` and as the first words of the body.
- **Every public declaration is anchored somewhere, exactly once.** The
  universe is the modules transitively imported by `KVAC.lean`; private and
  auto-generated declarations are exempt (the manifest script encodes this).
- **Anchors are comma-separated, fully qualified** in one
  `(lean := "A, B, C")` field.
- **Group bodies are titles.** A `:::group` body becomes the graph cluster
  label verbatim; keep it to a short phrase and put prose outside the block.
- **Theorem-kind nodes need a `:::proof` block**, milestones included; the
  summary flags them as missing informal coverage otherwise.
- **Unformalized nodes** carry `(effort := …)` and `(priority := …)` for the
  summary's triage; remove both when the node gains anchors.
- **`strictResolve` stays on** (`set_option
  verso.blueprint.externalCode.strictResolve true` in every chapter file), so
  renamed or missing anchors fail the build instead of warning.
- **Markdown gotcha**: a bare `_` inside prose is an emphasis delimiter and a
  build error; backtick identifiers like `MAC_GGM`, `R_iu`.
- Graph direction default is `LR`; readers can switch at runtime.

## Tooling

- `scripts/blueprint_decl_manifest.lean` — walks the compiled environment and
  prints every public source-backed declaration (`module<TAB>name`). The
  ground truth for coverage; environment-based because grepping source misses
  `noncomputable`/attributed declarations and cannot resolve duplicate short
  names.
- `scripts/blueprint_coverage_check.py` — diffs the manifest against the
  union of all `(lean := …)` lists in `docs/KVACDocs/*.lean`; nonzero exit on
  any missing, phantom, or duplicated declaration.
- `.github/workflows/docs-ci.yml` — runs both plus the full docs build and
  site generation on every PR touching `KVAC/**` or `docs/**`.

## Decision records

- **§3.1 assumptions anchored despite deferred q-DDHI** (2026-07). q-DDHI is
  needed only for μBBS/HashDY and is deferred with that scheme; DDH is
  consumed from VCV-io upstream. The node body states both. Alternative
  (milestone + unanchored element) rejected as noise.
- **Σ-protocol instances live in the μCMZ chapter** (2026-07). The merged
  protocols are scheme-specific instances of VCV-io's upstream
  `SigmaProtocol`; the Proof-systems chapter cross-references them via
  `bpref` and keeps its Track-Σ TODOs for the generic FS transform and
  straight-line extraction.
- **Registry covers all undimmed tracker elements** (2026-07). Unformalized
  elements are registered as unanchored stubs so the summary's denominator is
  honest; content and anchors are written for merged work only.

## Pending updates ledger

- **PR #54** (`Core/NIZKP/Extraction.lean`, ~22 declarations): on merge, add
  `ksnd_game` and `se_game` milestone nodes under `core_zkproof`, update the
  `zk_arguments` element (then complete), and drop the two "#54 in review"
  TODO notes (Core and Preliminaries).
- **`AGMReduction`** (branch exists): on merge, anchor `single_attribute_mac`
  (Lemma 5.4), extend `partial_evaluation_psi` with the restored ≤3-roots
  bound, and update the CMZ-M TODO.
- **Upstream nits found by the docs build**: stale docstring at
  `AGMPolynomial.lean:412` citing the removed
  `card_roots_affineSubst_verifPoly_le`; anchored structure fields and
  constructors lacking docstrings (`UFQuery.sign`, `AGMQuery.help`, …)
  produce build warnings.

Keep this ledger current: when an entry ships, delete it here and record any
new decision above.
