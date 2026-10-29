/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Security

/-!
# O24 Theorem 5.1: μCMZ is UF-CMVA in the game with Help

`microCMZ_ufcmvaHelp_le` states O24 Theorem 5.1 for the game with `Help` of
`UFCMVAHelp.lean` (`UF_CMVAHelpAdv`), the game the paper proves it for (p. 35). An
algebraic adversary `A : AGMUFAdversary` enters that game as `A.forget gen`, which
evaluates the representations `A` submits. The algebraic group model enters only through
the adversary type: `UF_CMVAHelpAdv_forget` equates the advantage of `A.forget gen` in
that game with the advantage of `A` in the AGM game, with no condition on `A`.

The bound is that of Lemma 5.5 (`agm_ufcmva_le_explicit`), against the same two named
reductions, `microCMZN3DLReduction` and `gapDlReduction`. It departs from O24's printed
`Adv^{3-dl} + Adv^{dl} + 3/p` as Lemma 5.5's does: the gap-DL term is explicit, the
constant is `5/p`, and there is no DL term (the module docstring of
`KVAC.Schemes.MicroCMZ.AGMReduction.Security` gives the reasons). The reductions are named
rather than quantified existentially, because a perfect discrete-log solver exists on a
finite group, so an existential bound would be vacuous
(`KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Statements`, *Why named reductions*).
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- **O24 Theorem 5.1.** For an algebraic adversary `A`, the advantage of `A.forget gen` in
the UF-CMVA game with `Help` against the μCMZ base MAC is at most the 3-DL advantage of
`microCMZN3DLReduction gen A` plus the gap-DL advantage of `gapDlReduction gen A` plus
`5/p`.

**Proof.** `UF_CMVAHelpAdv_forget` equates the advantage with the AGM advantage
`AGM_UF_CMVAAdv gen A secParam`, which Lemma 5.5, `agm_ufcmva_le_explicit`, bounds by the
same right-hand side. -/
theorem microCMZ_ufcmvaHelp_le (secParam : ℕ) (A : AGMUFAdversary F G n) :
    UF_CMVAHelpAdv gen (A.forget gen) secParam ≤
      microCMZN3DLReductionAdv gen A + gapDlogAdv gen (gapDlReduction gen A) +
        5 * (Fintype.card F : ℝ≥0∞)⁻¹ :=
  (UF_CMVAHelpAdv_forget gen secParam A).trans_le (agm_ufcmva_le_explicit gen secParam A)

end KVAC.Schemes.MicroCMZ
