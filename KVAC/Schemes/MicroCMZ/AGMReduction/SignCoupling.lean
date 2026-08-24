/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Coupling

/-!
# μCMZ AGM unforgeability — the deterministic core, sign arm (Piece A)

The *deterministic* half of the reduction ↔ honest-game coupling, for the `sign`
oracle arm and the transcript invariants it establishes.

`macScalar_maskedKey_expand` is the hinge between the two normal forms of the
masked key scalar. What this file states speaks the `macScalar (maskedKey …)`
form that `Coupling`'s `redLogHonestInv` uses, so a caller holding the state
invariant never has to convert; the abstract-arity lemmas underneath — `Core`'s
`agmRepr_eval_eq_eval_toPoly` — want the key spelled out as `x₀ + xᵣ + m·x₁`
instead, and this is the lemma that trades one form for the other.

Everything here is `evalDist`-free algebra; the probability layer sits above it.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F]

/-! ## Deterministic core (Piece A) -/

/-- **The masked key scalar, expanded.** `Coupling`'s `macScalar_maskedKey_eq` in the *other* normal
form: `redLogHonestInv`, and everything stated in this file, speak
`macScalar (maskedKey x aM bM)`, while the abstract-arity consistency lemmas — `Core`'s
`agmRepr_eval_eq_eval_toPoly` and its companions — take their `htag` with the key spelled out as
`x₀ + xᵣ + m·x₁` at the masked secrets `xₖ = aₖ + x·bₖ`. This is the one lemma that trades one
spelling for the other, so the `ring` step lives here instead of at every call site. It also
witnesses that the scalar depends on `m` only through `m 0`, which is what lets the `Fin 1`
transcript index and an `F`-valued message list line up. -/
lemma macScalar_maskedKey_expand (aM bM : FixedMasks F) (x : F) (m : Fin 1 → F) :
    macScalar (maskedKey x aM bM) m
      = (aM.x0 + x * bM.x0) + (aM.xr + x * bM.xr) + m 0 * (aM.x1 + x * bM.x1) := by
  simp only [macScalar, Fin.sum_univ_one]
  ring

end KVAC.Schemes.MicroCMZ
