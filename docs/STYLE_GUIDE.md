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

### Prime-order group convention

Throughout the formalisation, the abstract setting of [O24](https://eprint.iacr.org/2024/1552) §3.1 — a prime-order abelian group `G` of order `p` with scalars in `ZMod p` (or a generic field `F` ≃ `ZMod p`) — is bundled into two `class abbrev`s in [`KVAC/Core/Group.lean`](../KVAC/Core/Group.lean):

```lean
class abbrev PrimeOrderGroup (F G : Type) [Field F] :=
  AddCommGroup G, Fintype G, IsAddCyclic G, IsSimpleAddGroup G, Module F G

class abbrev SampleableGroup (F G : Type)
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] :=
  PrimeOrderGroup F G, SampleableType G
```

Each file uses **one** of two canonical `variable` blocks. There are no opt-in variants — the class signature lists everything the call site needs, so a missing binder produces a clear elaboration error rather than silent under-specification.

**Non-game files** (`Core/`, `Framework/Syntax`, `Framework/Correctness`, `Schemes/*/Construction`, …) — use `PrimeOrderGroup`:

```lean
variable {F G : Type} [Field F] [PrimeOrderGroup F G]
```

**Game-construction files** (`Framework/Anonymity`, `Framework/Extractability`, scheme `Anonymity` / `Extractability` / `OneMoreUnforgeability`, …) — use `SampleableGroup`, with the full F-side and `DecidableEq G` binders it requires:

```lean
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
```

What the binders give you (some bundled, some required at the call site):

- `[AddCommGroup G]` (bundled) — abelian additive group.
- `[Fintype G]` (bundled) — finite, so `Nat.card G` is well-defined.
- `[IsAddCyclic G]` (bundled) — cyclic. Derivable from `[AddCommGroup G] [Fintype G] [IsSimpleAddGroup G]` via Mathlib's "simple abelian finite ⇒ cyclic of prime order" instance; bundled for self-documentation.
- `[IsSimpleAddGroup G]` (bundled) — for a finite abelian group, equivalent to `G ≃ ZMod p` for a prime `p`. This is what pins down "prime order".
- `[Field F] [Module F G]` (binder + bundled) — scalars in the field `F`. `x • g` works out of the box for `x : F`, `g : G`, and the full Mathlib `Module` lemma library (`mul_smul`, `add_smul`, `one_smul`, `smul_add`, …) is available. Concrete instantiations pick `F := ZMod p` for the appropriate `p`.
- (`SampleableGroup` only) `[Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableType G]` (binders + last one bundled) — VCV-io's sampling typeclasses for `F` and `G`, plus decidable equality on both. Lets you write `let x ←$ᵗ F; let g ←$ᵗ G; …` inside an `OracleComp` block, and pattern-match decidably on elements of either type.

Why the F-side classes and `DecidableEq` aren't bundled as `class abbrev` parents: `DecidableEq` is not a structure-class and can't appear as a parent; the F-side classes can't be bundled because `class abbrev`'s parents must share a single carrier (and `SampleableGroup`'s parents have carrier `G`). Requiring them as instance binders gives Lean's elaborator a clear error when one is missing.

**Use the `Add`-prefixed typeclasses.** Mathlib's `IsCyclic` and `IsSimpleGroup` are multiplicative-only — their class signatures require `[Pow G ℤ]` and `[Group G]` respectively, neither of which an `AddCommGroup G` provides. Using them in an additive context fails to elaborate (`failed to synthesize Pow G ℤ`). The additive counterparts `IsAddCyclic` (requires `[SMul ℤ G]`, provided by `AddCommGroup`) and `IsSimpleAddGroup` (requires `[AddGroup G]`) are the correct choice. Mathlib's `@[to_additive]` keeps the *theorems* in sync across the two notations, but typeclass names themselves are distinct.

[mathlib-style]: https://leanprover-community.github.io/contribute/style.html
[mathlib-naming]: https://leanprover-community.github.io/contribute/naming.html
