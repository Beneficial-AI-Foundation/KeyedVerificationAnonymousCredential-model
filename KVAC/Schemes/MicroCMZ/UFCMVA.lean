/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMBridge

/-!
# O24 Theorem 5.1: μCMZ is UF-CMVA in the plain game

`microCMZ_ufcmva_le_of_wellBehaved` states O24 Theorem 5.1 as the paper states it: for
algebraic adversaries, μCMZ is UF-CMVA secure **in the plain Figure 5 game** of
`KVAC.Core.AlgebraicMAC.Security` (`UF_CMVAAdv`). An `AGMUFAdversary` enters that game through
its forgetful translation `AGMUFAdversary.toUFAdversary`, and the AGM heuristic is isolated in
the explicit `WellBehaved` hypothesis.

The bound departs from O24's printed `Adv^{3-dl} + Adv^{dl} + 3/p` as Lemma 5.5's does (the
gap-DL term is explicit, the constant is `5/p`, there is no DL term); the departures are
listed in the module docstring of `KVAC.Schemes.MicroCMZ.AGMReduction.Security`.

The theorem sits in its own file, apart from the `AGMBridge` vocabulary, because its proof
needs `AGMReduction`, whose polynomial-heavy instance context the bridge development avoids.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/-- **O24 Theorem 5.1.** For a well-behaved algebraic adversary `A` (`WellBehaved`: truthful
representations, no Help queries, consistent forgeries), the *plain* UF-CMVA advantage
(O24 Figure 5, `KVAC.Core.UF_CMVAAdv`) of its translation `A.toUFAdversary gen` against the
μCMZ base MAC is bounded by a 3-DL advantage plus a gap-DL advantage plus `5/|F|` statistical
slack. The AGM assumption appears only as the explicit `WellBehaved` hypothesis. The witnesses
are the reductions of `agm_ufcmva_le_explicit`: `microCMZN3DLReduction gen A` in
`QDLogAdversary` shape at base `gen` (as in `microCMZN3DLReductionExp`), and
`gapDlReduction gen A`.

**Proof outline.** Under `WellBehaved`, the plain advantage of `A.toUFAdversary gen` equals
the AGM advantage `AGM_UF_CMVAAdv gen A` (the AGM↔plain bridge, #81), and Lemma 5.5,
`agm_ufcmva_le_explicit`, bounds the latter. -/
theorem microCMZ_ufcmva_le_of_wellBehaved (A : AGMUFAdversary F G n)
    (hA : WellBehaved gen secParam A) :
    ∃ (B₃ : QDLogAdversary 3 F G) (Bgap : GapDLogAdversary F G),
      UF_CMVAAdv (μCMZBaseMACSyntax F gen) (A.toUFAdversary gen) secParam n ≤
        qdlogAdv 3 gen B₃ + gapDlogAdv gen Bgap + 5 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  sorry

end KVAC.Schemes.MicroCMZ
