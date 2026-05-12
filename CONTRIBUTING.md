# Contributing to KeyedVerificationAnonymousCredential-model

We can all benefit in many ways from interacting with each other! Contributions are very welcome.

This project formalizes, in Lean 4, the keyed-verification anonymous credential (KVAC) framework of [Orrù, *Revisiting Keyed-Verification Anonymous Credentials* (IACR ePrint 2024/1552)](https://eprint.iacr.org/2024/1552), together with two concrete instantiations (μCMZ and μBBS).

- For an orientation to the project, read the [formalization plan](docs/PLAN.md). For the current status of each track and to claim work, see the [tracks board](docs/TRACKS.md).

- Repo contributions follow the standard fork-and-PR method. Details on our operational workflow and how to prepare PRs are in the [Workflow and PR Guide](docs/WORKFLOW_AND_PR_GUIDE.md).

- Details on expected file-, code-, comment-, and theorem-style are in the [Style Guide](docs/STYLE_GUIDE.md).

## Building

```bash
lake build
```

The first build fetches [Mathlib](https://github.com/leanprover-community/mathlib4) and may take 10–20 minutes. Subsequent builds use the cache.

## Questions

Open a discussion on the issue tracker, or reach out via the [Signal Shot Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/583276-Signal-Shot).
