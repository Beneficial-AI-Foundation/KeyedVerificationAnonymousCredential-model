# KeyedVerificationAnonymousCredential-model

A Lean 4 formalization of the keyed-verification anonymous credential (KVAC) framework of [Orrù, *Revisiting Keyed-Verification Anonymous Credentials* (IACR ePrint 2024/1552)](https://eprint.iacr.org/2024/1552), together with two concrete instantiations (μCMZ and μBBS).

**Status.** Early stage. The formalization plan is a tentative working proposal — see [`docs/PLAN.md`](docs/PLAN.md) for what is being built and [`docs/TRACKS.md`](docs/TRACKS.md) for the current state of each parallel work track.

## Building

```bash
lake build
```

Requires the Lean 4 toolchain pinned in [`lean-toolchain`](lean-toolchain) (currently `v4.28.0-rc1`); install via [elan](https://github.com/leanprover/elan). The first build fetches [Mathlib](https://github.com/leanprover-community/mathlib4) and may take 10–20 minutes; subsequent builds use the cache.

[`curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify) is **not** a Lake dependency at this stage — it is added later when the Examples/ track lands. See [`docs/PLAN.md`](docs/PLAN.md) for the rationale.

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
