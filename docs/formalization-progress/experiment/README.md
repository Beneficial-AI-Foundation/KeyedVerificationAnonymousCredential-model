# KeyedVerificationAnonymousCredential-model

A Lean 4 formalization of the keyed-verification anonymous credential (KVAC) framework of [Orrù, *Revisiting Keyed-Verification Anonymous Credentials* (IACR ePrint 2024/1552)](https://eprint.iacr.org/2024/1552), together with two concrete instantiations (μCMZ and μBBS).

The formalization plan is a tentative working proposal — see [`docs/PLAN.md`](docs/PLAN.md) for what is being built.

## Building

```bash
lake build
```

Requires the Lean 4 toolchain pinned in [`lean-toolchain`](lean-toolchain) (currently `v4.28.0-rc1`); install via [elan](https://github.com/leanprover/elan). The first build fetches [Mathlib](https://github.com/leanprover-community/mathlib4) and may take 10–20 minutes; subsequent builds use the cache.

## Documentation

The Verso blueprint at https://beneficial-ai-foundation.github.io/KeyedVerificationAnonymousCredential-model/ is the live, rendered view of the formalization, with per-chapter prose tied to the Lean declarations as they land. The markdown documents below cover the formalization plan, work breakdown, and contribution workflow.

| File                                                              | What it is                                                                                                                                              |
| ----------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [`docs/README.md`](docs/README.md)                               | Build instructions for the Verso blueprint site and the "Adding a new chapter" recipe.                                                                  |
| [`docs/PLAN.md`](docs/PLAN.md)                                   | The canonical formalization plan: paper background, module layout with dependency graph, module breakdown, security results targeted, and future works. |
| [`docs/TRACKS.md`](docs/TRACKS.md)                               | Status board for parallel work tracks, with a Mermaid dependency graph and per-track checkboxes.                                                        |
| [`docs/STYLE_GUIDE.md`](docs/STYLE_GUIDE.md)                     | Code, comment, and theorem style conventions.                                                                                                           |
| [`docs/WORKFLOW_AND_PR_GUIDE.md`](docs/WORKFLOW_AND_PR_GUIDE.md) | Branching conventions, build expectations, PR title and footer format.                                                                                  |
| [`CONTRIBUTING.md`](CONTRIBUTING.md)                             | How to claim work, where to ask questions, and a guided entry point into the docs above.                                                                |
| [`docs/formalization-progress/`](docs/formalization-progress/FORMALIZATION_PROGRESS.md) | Generated progress table mapping each paper element (Orrù 2024) to the Lean declaration that formalizes it, with completion status. |

## Contributing

Contributions are very welcome. Start by reading [`CONTRIBUTING.md`](CONTRIBUTING.md), then pick a track from [`docs/TRACKS.md`](docs/TRACKS.md). Reach out via the [Signal Shot Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/583276-Signal-Shot) before starting work — especially on Track 0 (Core typeclasses) or Track Σ (sigma-protocol DSL), whose API shapes are reviewed centrally before any track that depends on them can begin.

## Status

> **Experiment — heuristic-derived, not canonical.** The tags below are applied
> from `FORMALIZATION_PROGRESS.md`, an approximate map (see its header). `🟢 O24 …`
> marks an element the tracker reports as *appearing* formalized; `🌀` a
> cited-but-kind-mismatched element; `⚪` nothing found. Each is a claim to review,
> not a verified fact. This is a scratch copy under
> `docs/formalization-progress/experiment/`; the canonical board is `README.md`.

When a track is split into sub-issues, list them as nested bullets under the track (as Track 0 is below).

- [ ] **Wave 0** — `KVAC/Core/` typeclasses 🚧 WIP
  - [X] `Core/Group.lean` ([#18]) — 🟢 O24 §3.1
  - [ ] `Core/Hash.lean` ([#19]) — ⚪ still a stub
  - [X] `Core/ZKProof.lean` ([#20])
  - [X] `Core/NIZKP/Basic.lean` ([#20]) — 🟢 O24 §3.3 (agnostic spec)
  - [X] `Core/AlgebraicMAC.lean` ([#21]) — 🟢 O24 Definition 3.1, Figure 5
- [ ] **Wave 1** — preliminaries, proof systems, framework correctness
  - [ ] Track Pre — Preliminaries ([#2]) — partial: 🟢 O24 §3.1 (Assumptions); ZK arguments, anonymous tokens, q-DDHI pending
  - [ ] Track Σ — ProofSystems ([#3]) — partial: 🟢 O24 Equation 9 (R_iu); R_is/R_p pending
  - [ ] Track F1 — Framework syntax and correctness ([#4]) — ⚪
- [ ] **Wave 2** — framework anonymity/extractability, scheme constructions
  - [ ] Track F2 — Framework anonymity and extractability ([#5]) — ⚪
  - [ ] Track CMZ-C — μCMZ construction ([#6]) — partial:
    - [x] Base MAC — 🟢 O24 Figure 9
    - [x] R_iu Σ-protocol — 🟢 O24 Equation 9
    - [ ] R_is / R_p Σ-protocols, issuance / presentation
  - [ ] Track BBS-C — μBBS construction ([#7]) — ⚪
- [ ] **Wave 3** — security tracks (μCMZ and μBBS)
  - [ ] Track CMZ-M — μCMZ as algebraic MAC (Theorem 5.1) ([#8]) — 🌀 O24 Theorem 5.1 (only the 3-DL assumption is formalized; the theorem is not)
  - [ ] Track CMZ-A — μCMZ anonymity (Theorem 5.8) ([#10]) — ⚪
  - [ ] Track CMZ-E — μCMZ extractability (Theorem 5.2) ([#11]) — ⚪
  - [ ] Track CMZ-OMUF — μCMZ one-more unforgeability (Theorem 5.3) ([#12]) — 🌀 O24 Theorem 5.3 (only the 2-DL assumption is formalized)
  - [ ] Track BBS-M — μBBS as algebraic MAC ([#13]) — ⚪
  - [ ] Track BBS-A — μBBS anonymity ([#14]) — ⚪
  - [ ] Track BBS-E — μBBS extractability ([#15]) — ⚪
  - [ ] Track BBS-OMUF — μBBS one-more unforgeability (Theorem 6.12) ([#16]) — ⚪
- [ ] **Wave 4** — concrete μCMZ run with Ristretto255
  - [ ] Track Ex — Concrete μCMZ run + Ristretto binding + Lake dependency ([#17]) — ⚪

Per-track status and dependency graph in [`TRACKS.md`](TRACKS.md).

## License

[MIT](LICENSE).

[#2]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/2
[#3]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/3
[#4]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/4
[#5]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/5
[#6]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/6
[#7]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/7
[#8]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/8
[#10]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/10
[#11]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/11
[#12]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/12
[#13]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/13
[#14]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/14
[#15]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/15
[#16]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/16
[#17]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/17
[#18]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/18
[#19]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/19
[#20]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/20
[#21]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/21
