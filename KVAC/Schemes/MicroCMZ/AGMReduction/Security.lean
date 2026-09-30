/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.AttributeCollapse
import KVAC.Schemes.MicroCMZ.AGMReduction.GapDLReduction

/-!
# μCMZ AGM unforgeability, general `n` — the Lemma 5.5 target statement (O24 §5.3)

This file states the general-`n` advantage bound the Lemma 5.5 modules exist to
prove:

  `AGM_UF_CMVAAdv gen A secParam ≤
     microCMZN3DLReductionAdv gen A + gapDlogAdv gen (gapDlReduction gen A) + 5/p`.

The bound speaks of the instrumented AGM(+Help) game `AGM_UF_CMVAGame` of
`AlgebraicMAC.lean`, as `SecurityN1` does for `n = 1`. Theorem 5.1 proper, this
bound for the plain Figure 5 game and `WellBehaved` algebraic adversaries, is
reached from this one through the AGM↔plain bridge tracked in #81.

The statement is added first, so that the two reductions it bounds by
(`microCMZN3DLReduction` of `AttributeCollapse`, `gapDlReduction` of
`GapDLReduction`) review against a visible target.

**Departures from O24's printed bound** (Theorem 5.1 and Lemma 5.5 print
`Adv^{3-dl} + Adv^{dl} + 3/p`, pp. 35 and 38):

- The gap-DL term is explicit. The paper's own proof of Lemma 5.5 sends the
  colliding-forgery case to gap-DL through Claim 5.6, so the assembled bound
  carries the advantage of `gapDlReduction`; the printed statement elides it
  (errata §6).
- The additive constant is `5/p`: `3/p` from Lemma 5.4 on the wrapper (the
  Schwartz–Zippel constant, errata §1 and `SecurityN1`'s module docstring)
  `+ 1/p` for the Claim 5.7 keygen-shear bad event `x₁ = 0` `+ 1/p` for the
  Claim 5.6 vanishing-denominator bad event (`gapDlReduction`'s docstring).
- There is no `Adv^dl` term: the proof reduces to 3-DL and to gap-DL, through
  the two reductions this file imports, and builds no DL reduction (for
  Lemma 5.4's part, `SecurityN1`'s module docstring); dropping the nonnegative
  `Adv^dl` summand only tightens the bound.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)
variable {n : ℕ}

/-! ## Lemma 5.5 -/

/-- **O24 Lemma 5.5** (μCMZ is UF-CMVA for any `n` in the AGM, instrumented game):
the AGM advantage of an `n`-attribute algebraic adversary is at most the 3-DL
advantage of `microCMZN3DLReduction gen A` plus the gap-DL advantage of
`gapDlReduction gen A` plus `5/p`.

**Proof outline.** Split a winning forgery `(m⃗*, σ*)` on whether its attribute
combination collides with that of a message queried to the MAC oracle:
`Σᵢ m*ᵢ•Xᵢ = Σᵢ mⱼ,ᵢ•Xᵢ` for some queried `m⃗ⱼ ≠ m⃗*`.

1. *Collision* (Claim 5.6): `gapDlReduction gen A` embeds the gap-DL challenge
   `X = x•g` into the parameters `Xᵢ = aaᵢ•g + bbᵢ•X`, answers the oracles through
   the DDH-decision oracle (`gapDlOracleImpl`, whose answers equal the honest
   answers on `verify`/`help` and are identically distributed on `sign`), and
   extracts `x = num·den⁻¹` from the collision relation. The bad
   event is the vanishing denominator `Σᵢ bbᵢ·(mⱼ,ᵢ − m*ᵢ) = 0`, degree 1 in the
   perfectly hidden `bb⃗`: probability at most `1/p`.
2. *No collision* (Claim 5.7): along a uniform direction `r⃗`, `nTo1Adversary gen A r`
   runs `A` against the 1-attribute game with `xᵢ = rᵢ·x₁`, translating each
   query's representation (`collapseOracleImpl`); for `x₁ ≠ 0` the key marginal is
   the honest one and a fresh, non-colliding `n`-attribute forgery collapses to a
   fresh 1-attribute forgery, so the win transfers. The excluded event `x₁ = 0`
   costs `1/p`.
3. *Lemma 5.4 on the wrapper*: `agm_ufcmva_le_n1_explicit` bounds each direction's
   1-attribute advantage by the 3-DL advantage of `microCMZ3DLReduction` plus
   `3/p`; `microCMZN3DLReduction` samples `r⃗` inside the 3-DL experiment, so by
   linearity the average is `microCMZN3DLReductionAdv gen A + 3/p`.

The statement also covers `n = 0`, which O24's Definition 4.2 excludes
(`n > 0`): no two messages differ, so no forgery collides, and step 2 applies
with `collapseMsg` sending the empty message to `0`, whose 1-attribute key
`x₀ + xᵣ` is the 0-attribute key.

Summing: `Adv(n) ≤ Adv^{3-dl} + Adv^{gap-dl} + 5/p`; the departures from O24's
printed bound are in the module docstring. -/
theorem agm_ufcmva_le_explicit (A : AGMUFAdversary F G n) :
    AGM_UF_CMVAAdv gen A secParam ≤
      microCMZN3DLReductionAdv gen A + gapDlogAdv (gen) (gapDlReduction gen A) +
        5 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  sorry

end KVAC.Schemes.MicroCMZ
