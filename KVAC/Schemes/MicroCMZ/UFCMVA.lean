/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMBridge
import KVAC.Schemes.MicroCMZ.AGMReduction.Security

/-!
# O24 Theorem 5.1: μCMZ is UF-CMVA in the plain game

`microCMZ_ufcmva_le_of_wellBehaved` states O24 Theorem 5.1 for the plain Figure 5 game of
`KVAC.Core.AlgebraicMAC.Security` (`UF_CMVAAdv`). An algebraic adversary `A : AGMUFAdversary`
enters that game through its forgetful translation `AGMUFAdversary.toUFAdversary`. The
algebraic group model enters twice: through the adversary type, which outputs a representation
for every group element it submits, and through the hypothesis `WellBehaved`, which makes those
representations truthful and rules out Help queries.

The bound is that of Lemma 5.5 (`agm_ufcmva_le_explicit`), against the same two named
reductions, `microCMZN3DLReduction` and `gapDlReduction`. It departs from O24's printed
`Adv^{3-dl} + Adv^{dl} + 3/p` as Lemma 5.5's does: the gap-DL term is explicit, the constant is
`5/p`, and there is no DL term (the module docstring of
`KVAC.Schemes.MicroCMZ.AGMReduction.Security` gives the reasons). The reductions are named
rather than quantified existentially, because a perfect discrete-log solver exists on a finite
group, so an existential bound would be vacuous (`OneMoreUnforgeability`, "Why named
reductions").

The theorem sits in its own file, apart from the `AGMBridge` vocabulary, because it imports
`AGMReduction`, whose polynomial-heavy instance context the bridge development avoids.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/-- **O24 Theorem 5.1.** For a well-behaved algebraic adversary `A`, the plain UF-CMVA
advantage (O24 Figure 5) of its translation `A.toUFAdversary gen` against the μCMZ base MAC is
at most the 3-DL advantage of `microCMZN3DLReduction gen A` plus the gap-DL advantage of
`gapDlReduction gen A` plus `5/p`.

**Proof outline.** Under `WellBehaved`, the plain advantage of `A.toUFAdversary gen` equals the
AGM advantage `AGM_UF_CMVAAdv gen A secParam` (the AGM↔plain bridge, #81), and Lemma 5.5,
`agm_ufcmva_le_explicit`, bounds the latter by the same right-hand side. -/
theorem microCMZ_ufcmva_le_of_wellBehaved (A : AGMUFAdversary F G n)
    (hA : WellBehaved gen secParam A) :
    UF_CMVAAdv (μCMZBaseMACSyntax F gen) (A.toUFAdversary gen) secParam n ≤
      microCMZN3DLReductionAdv gen A + gapDlogAdv gen (gapDlReduction gen A) +
        5 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  sorry

end KVAC.Schemes.MicroCMZ
