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

When a track is split into sub-issues, list them as nested bullets under the track. A checked track means its issue is closed and its deliverables are on `main`. Declaration-level progress is computed by the [blueprint](https://beneficial-ai-foundation.github.io/KeyedVerificationAnonymousCredential-model/). This list tracks issues only.

- [x] **Wave 0** — `KVAC/Core/` typeclasses ([#1])
  - [x] `Core/Group.lean` ([#18])
  - [x] `Core/Hash.lean` ([#19])
  - [x] `Core/ZKProof.lean` ([#20])
  - [x] `Core/NIZKP/Basic.lean` ([#20])
  - [x] `Core/AlgebraicMAC.lean` ([#21])
- [ ] **Wave 1** — preliminaries, proof systems, framework correctness
  - [x] Track Pre — Preliminaries ([#2]); the §3.4 anonymous-token items continue under Track CMZ-OMUF ([#144], [#145])
  - [ ] Track Σ — Proof systems ([#3]); being rescoped: the concrete Σ-protocols landed under Track CMZ-C and the NIZKP games under `Core/NIZKP/`, the Fiat–Shamir transform and §9 straight-line extraction remain
  - [x] Track F1 — Framework syntax and correctness ([#4])
- [ ] **Wave 2** — framework anonymity/extractability, scheme constructions
  - [ ] Track F2 — Framework anonymity and extractability ([#5])
    - [x] Extraction game, Definition 4.5 and Figure 8 ([#117])
    - [ ] Partial-disclosure predicate family, Definition 4.2 ([#104])
    - [ ] Anonymity game, Definition 4.4
  - [ ] Track CMZ-C — μCMZ construction ([#6])
    - [x] Base MAC ([#39])
    - [x] R_iu Σ-protocol, Eq. 9 ([#40])
    - [x] R_is and R_p Σ-protocols, Eqs. 10 and 11 ([#41])
    - [ ] μCMZ `KVACSyntax` instance, Issuance and Presentation with π_iu, π_is, π_p ([#163])
  - ~~Track BBS-C~~ — μBBS descoped from v1 ([#7], closed as not planned)
- [ ] **Wave 3** — security tracks (μCMZ)
  - [ ] Track CMZ-M — μCMZ as algebraic MAC, Theorem 5.1 ([#8]); AGM game, polynomial backbone, reduction core and coupling merged, Lemma 5.4 bound stated (PR #155), open sub-issues [#80], [#81], [#107] to [#116]
  - [ ] Track CMZ-A — μCMZ anonymity, Theorem 5.8 ([#10])
  - [ ] Track CMZ-E — μCMZ extractability, Theorem 5.2 ([#11])
  - [ ] Track CMZ-OMUF — μCMZ one-more unforgeability, Theorem 5.3 ([#12])
    - [x] Anonymous-token syntax and correctness, §3.4 ([#144])
    - [ ] One-more unforgeability game, Figure 6 ([#145], PR #143)
    - [ ] Base MAC utilities for the core scheme ([#164], PR #146)
    - [ ] μCMZ_AT core scheme, §5.6 ([#165], PR #147)
  - ~~Tracks BBS-M, BBS-A, BBS-E, BBS-OMUF~~ — μBBS descoped from v1 ([#13], [#14], [#15], [#16], closed as not planned; see the future tracks in [`docs/TRACKS.md`](docs/TRACKS.md))
- [ ] **Wave 4** — concrete μCMZ run with Ristretto255
  - [ ] Track Ex — Concrete μCMZ run + Ristretto binding + Lake dependency ([#17])

Per-track status and dependency graph in [`docs/TRACKS.md`](docs/TRACKS.md).

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
[#1]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/1
[#39]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/39
[#40]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/40
[#41]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/41
[#80]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/80
[#81]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/81
[#104]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/104
[#107]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/107
[#116]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/116
[#117]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/117
[#144]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/144
[#145]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/145
[#163]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/163
[#164]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/164
[#165]: https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model/issues/165
