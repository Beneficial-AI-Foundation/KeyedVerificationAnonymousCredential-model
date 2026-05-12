# KeyedVerificationAnonymousCredential-model

A Lean 4 formalization of the keyed-verification anonymous credential (KVAC) framework of [Orrù, *Revisiting Keyed-Verification Anonymous Credentials* (IACR ePrint 2024/1552)](https://eprint.iacr.org/2024/1552), together with two concrete instantiations (μCMZ and μBBS).

The formalization plan is a tentative working proposal — see [`docs/PLAN.md`](docs/PLAN.md) for what is being built.

## Status

When a track is split into sub-issues, list them as nested bullets under the track (as Track 0 is below).

- [ ] **Wave 0** — `KVAC/Core/` typeclasses 🚧 WIP
    - [ ] `Core/Group.lean` (#18) 🚧 WIP
    - [ ] `Core/Hash.lean` (#19)
    - [ ] `Core/ZKProof.lean` (#20)
    - [ ] `Core/AlgebraicMAC.lean` (#21)
- [ ] **Wave 1** — preliminaries, proof systems, framework correctness
    - [ ] Track Pre — Preliminaries (#2)
    - [ ] Track Σ — ProofSystems (#3)
    - [ ] Track F1 — Framework syntax and correctness (#4)
- [ ] **Wave 2** — framework anonymity/extractability, scheme constructions
    - [ ] Track F2 — Framework anonymity and extractability (#5)
    - [ ] Track CMZ-C — μCMZ construction (#6)
    - [ ] Track BBS-C — μBBS construction (#7)
- [ ] **Wave 3** — security tracks (μCMZ and μBBS)
    - [ ] Track CMZ-M — μCMZ as algebraic MAC (Theorem 5.1) (#8)
    - [ ] Track V — VCV-io oracle binding (#9)
    - [ ] Track CMZ-A — μCMZ anonymity (Theorem 5.8) (#10)
    - [ ] Track CMZ-E — μCMZ extractability (Theorem 5.2) (#11)
    - [ ] Track CMZ-OMUF — μCMZ one-more unforgeability (Theorem 5.3) (#12)
    - [ ] Track BBS-M — μBBS as algebraic MAC (#13)
    - [ ] Track BBS-A — μBBS anonymity (#14)
    - [ ] Track BBS-E — μBBS extractability (#15)
    - [ ] Track BBS-OMUF — μBBS one-more unforgeability (Theorem 6.12) (#16)
- [ ] **Wave 4** — concrete μCMZ run with Ristretto255
    - [ ] Track Ex — Concrete μCMZ run + Ristretto binding + Lake dependency (#17)

Per-track status and dependency graph in [`docs/TRACKS.md`](docs/TRACKS.md).

## Building

```bash
lake build
```

Requires the Lean 4 toolchain pinned in [`lean-toolchain`](lean-toolchain) (currently `v4.28.0-rc1`); install via [elan](https://github.com/leanprover/elan). The first build fetches [Mathlib](https://github.com/leanprover-community/mathlib4) and may take 10–20 minutes; subsequent builds use the cache.

## Documentation

| File | What it is |
|---|---|
| [`docs/PLAN.md`](docs/PLAN.md) | The canonical formalization plan: paper background, module layout with dependency graph, module breakdown, security results targeted, and future works. |
| [`docs/TRACKS.md`](docs/TRACKS.md) | Status board for parallel work tracks, with a Mermaid dependency graph and per-track checkboxes. |
| [`docs/STYLE_GUIDE.md`](docs/STYLE_GUIDE.md) | Code, comment, and theorem style conventions. |
| [`docs/WORKFLOW_AND_PR_GUIDE.md`](docs/WORKFLOW_AND_PR_GUIDE.md) | Branching conventions, build expectations, PR title and footer format. |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | How to claim work, where to ask questions, and a guided entry point into the docs above. |

## Contributing

Contributions are very welcome. Start by reading [`CONTRIBUTING.md`](CONTRIBUTING.md), then pick a track from [`docs/TRACKS.md`](docs/TRACKS.md). Reach out via the [Signal Shot Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/583276-Signal-Shot) before starting work — especially on Track 0 (Core typeclasses) or Track Σ (sigma-protocol DSL), whose API shapes are reviewed centrally before any track that depends on them can begin.

## License

[MIT](LICENSE).
