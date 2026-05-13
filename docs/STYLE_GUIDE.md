# Style Guide

## General style

We follow the [Mathlib style guide][mathlib-style] with the additions below.

### File header and imports

File headers should be of the form:

```lean
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Joe Cool
-/
```

The copyright holder is the author or their current employer. Authors who have made significant contributions to a file should be added in chronological order based on when they edited it. AI tools are not listed as authors. There are no strict rules on what qualifies as a significant contribution; the people listed should be those we would reach out to with questions about the design or development of the file.

### File organisation

- The `KVAC/` directory mirrors the structure of [O24](https://eprint.iacr.org/2024/1552): `Core/` (abstract typeclass API), `Preliminaries/` (assumptions and ZK arguments), `ProofSystems/` (sigma protocols), `Framework/` (paper-level KVAC syntax and security definitions), `Schemes/MicroCMZ/` and `Schemes/MicroBBS/` (the two concrete schemes), `Instances/` (Ristretto255 and VCV-io bindings), and `Examples/` (runnable code). See [`PLAN.md`](PLAN.md) for the rationale.
- File names are `UpperCamelCase.lean` and match the concept they define (`Group.lean`, `AlgebraicMAC.lean`, `Construction.lean`).
- Multiple closely related theorems may live in the same file, but a file should have a single coherent topic.

### Avoiding flexible tactics

Flexible (non-terminal) tactics make proofs fragile and harder to maintain. Avoid them as much as possible:

- **`simp`**: use `simp?` to obtain the explicit lemma list, then replace with `simp only [...]`. This makes the proof deterministic and resistant to changes in the global simp set.
- **`simp_all`**: use `simp_all?` to obtain `simp_all only [...]`.
- **`grind`**: prefer more targeted alternatives (`omega`, `ring`, `linear_combination`, `decide`) where feasible.
- **`exact?` / `apply?`**: use these *interactively* to discover the right lemma, then replace with the explicit `exact` or `apply` call.

When a flexible tactic is genuinely the best option (for example a `simp` that closes a goal whose explicit lemma list would be impractically long), document why in a short comment.

### Linters

Linter warnings should be **resolved, not suppressed**. Avoid `#check`/`#eval` leftovers and `set_option linter.* false` unless there is a clear justification documented in a comment.

### Heartbeats

Keep `set_option maxHeartbeats` increases to the bare minimum needed. Use multiples of **200000** as a standard increment (e.g. 400000, 800000). If a proof requires a very large heartbeat budget, consider refactoring it into helper lemmas to bring the cost down.

### Formatting

- Lines should be at most 100 characters.
- Imports follow immediately after the file header without empty lines.
- Definitions and theorems follow the [Mathlib naming guidelines][mathlib-naming]: `lowerCamelCase` for definitions, `lowercase_underscored` for theorems whose name is a sentence (e.g. `verify_correct`), `lowerCamelCase` for theorems whose name is a proper noun (e.g. `MAC.completeness`).

## Notation conventions

### Additive groups

The formalisation uses **additive notation** for all groups, matching the convention of [O24](https://eprint.iacr.org/2024/1552) §3.1. Concretely:

| Paper                    | Lean                          |
|--------------------------|-------------------------------|
| `G ∈ G` (generator)      | `(generator : G)`             |
| `xG` (scalar mult)       | `x • generator`               |
| `aP + bP = (a+b)P`       | `a • P + b • P = (a+b) • P`   |
| `0G = 0` (identity)      | `(0 : G)`                     |

When porting equations from a multiplicative-style reference, apply this translation rule:

- paper `·` (group op) → Lean `+`,
- paper `^` (exponentiation) → Lean `•` (scalar action), with the operand order **flipped**: paper `g^x` ↔ Lean `x • g`.

The multiplicative group `(ZMod p)*`, when it appears, stays multiplicative.

**Why additive.** Mathlib's elliptic-curve types are `AddCommGroup`. The dalek Ristretto255 API is additive. Choosing additive at the abstract layer makes Track Ex's concrete instantiation a direct match with no notation flips.

[mathlib-style]: https://leanprover-community.github.io/contribute/style.html
[mathlib-naming]: https://leanprover-community.github.io/contribute/naming.html
