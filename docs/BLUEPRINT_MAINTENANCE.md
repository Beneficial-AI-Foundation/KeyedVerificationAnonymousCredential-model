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

## Landing page dashboard

The site's root `index.html` is generated at deploy time by
`scripts/blueprint_dashboard.py` from the blueprint manifest
(`html-multi/-verso-data/blueprint-manifest.json`) plus a progress-history
JSON — it is not a checked-in file and not the Verso output. Modeled on the
secure-messaging landing page.

- **Counter contracts** (all read from Verso-computed node statuses, never
  recomputed): specified = `statementStatus ∈ {formalized, mathlib}`;
  verified = `proofStatus ∈ {formalized, formalizedWithAncestors}`; fully
  closed = `formalizedWithAncestors`; deps pending = `formalized`; ready =
  either axis `ready`; sorries = `incomplete`. docs-ci asserts the landing
  counters equal the rendered Blueprint-Summary numbers.
- **History**: `scripts/blueprint_progress_history.py update` merges the
  committed seed (`docs/blueprint-progress-seed.json`, a one-time reviewed
  git backfill against a fixed basis, every point marked `estimated`) with
  the previously deployed `blueprint-progress-history.json` (fetched from
  the live site) and the exact HEAD snapshot, which always wins for its own
  commit. Recovery guarantees: a clean 404 is bootstrap; any other fetch
  failure **fails the deploy** (rerun it) rather than publishing a lossy
  seed+HEAD document; a merge may never reduce the number of exact
  snapshots. Residual risk: a post-bootstrap 404 (Pages serving 404 for a
  file it used to serve) is indistinguishable from bootstrap. Registry
  growth is recorded automatically as dated `basisChanges` entries in the
  output document; never edit the seed to "fix" history.
- **Deliberate semantic differences from the Blueprint Summary page** (both
  excluded from the CI conformance check): the landing's "Ready to start" =
  either axis `ready` (matches the table's Ready-next columns), while the
  Summary's "Ready now" is actionable-stage gated; the Summary's "no proof"
  counts theorem-like stubs only. Compared and enforced equal: total
  entries, completed, deps incomplete, sorries.
- **Chapters**: a node's chapter is the first path component of its manifest
  `href`; the mapping lives in `CHAPTER_ORDER`/`CHAPTER_TITLES` in the
  dashboard script. Adding a chapter to the manual means extending that
  mapping (the script fails loudly otherwise). Chapters without registry
  nodes render as "no registry entries yet".
- **Local preview**: generate the site (step 6 above with `--output _out/site`),
  then
  `python3 scripts/blueprint_progress_history.py update --site docs/_out/site`
  and `python3 scripts/blueprint_dashboard.py --site docs/_out/site`, then
  serve `docs/_out/site`.

## Decision records

- **§3.1 assumptions anchored despite deferred q-DDHI** (2026-07). q-DDHI is
  needed only by the §8.2 rate-limiting extension (HashDY PRF, Theorem 8.7)
  and is deferred with that extension; DDH is
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
- **`keyed_setup` is a milestone, not a paper element** (2026-08).
  `KeyedSetupSyntax` factors the CRS/keygen preamble shared by O24
  Definition 3.1 and Definition 4.2; it states no paper element of its own,
  so it is a `milestone` node under `core_keyed_setup` that `algebraic_mac`
  and `credential_predicate` both `uses`. Alternative (folding it into
  `algebraic_mac`) rejected: the graph would then hide the framework's
  dependency on the shared setup.
- **`kvac_correctness` anchored despite the deferred family-scope clause**
  (2026-08). O24 Definition 4.3 also requires `Φ ⊇ {φ_a⃗}`, which the
  abstract layer does not exhibit. `Correct` is stated for all `φ`, `φ'`, so
  it states the correctness experiment in full and never needs those members
  to exist; the obligation is carried by the scheme instances and recorded in
  the node's Tracks CMZ-C / BBS-C TODO.

## Pending updates ledger

- **PR #54** (`Core/NIZKP/Extraction.lean`, ~22 declarations): on merge, add
  `ksnd_game` and `se_game` milestone nodes under `core_zkproof`, update the
  `zk_arguments` element (then complete), and drop the two "#54 in review"
  TODO notes (Core and Preliminaries).
- **`AGMReduction`** (PR #88, issue #89, in review): delivers the Lemma 5.4
  reduction core only (the probability bound and the security theorems come
  later, #80/#81). On merge, add a reduction-core `milestone` node, extend
  `partial_evaluation_psi` with the restored ≤3-roots bound, and update the
  CMZ-M TODO; `single_attribute_mac` stays unanchored until the full lemma
  lands (anchoring honesty rule).
- **Upstream nits found by the docs build**: anchored structure fields and
  constructors lacking docstrings (`UFQuery.sign`, `AGMQuery.help`, …)
  produce build warnings.

Keep this ledger current: when an entry ships, delete it here and record any
new decision above.
