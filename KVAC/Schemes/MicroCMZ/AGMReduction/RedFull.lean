/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Coupling

/-!
# μCMZ AGM reduction — the analysis experiment (`redFull`)

`redFull` is the probability experiment the Lemma 5.4 proof skeleton
(`AGMReduction/SecurityN1.lean`) is assembled over: the reduction's run `redTrace`
at the genuine challenge powers, with the challenge exponent `x` in scope and the
trace kept, returning the record `RedBits` — the win bit, the extraction bit, the
Schwartz–Zippel bad bit, and the shift bit. Every Lemma 5.4 sub-lemma is an event
on these fields.

Its extraction marginal, `redFull_recBit_eq`, is stated and proven in `SecurityN1.lean`.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- The bits an analysis run of the reduction returns, for the forgery's verification
polynomial `φ` and its masked univariate `ψ` (`RedTrace.verifPoly`, `RedTrace.psi`). -/
structure RedBits where
  /-- The `AGM_UF_CMVAGame` predicate (consistency ∧ freshness ∧ `verify`) with the embedded
  points `ep` and the reduction's `log` in place of the honest `pp` and log, on the key the
  masks embed at the challenge exponent. -/
  winBit : Bool
  /-- The reduction's extraction success `recoverDlog gen X ψ = x`. -/
  recBit : Bool
  /-- The Schwartz–Zippel bad event `φ ≠ 0 ∧ ψ = 0`. -/
  badBit : Bool
  /-- The shift event `φ ≠ 0 ∧ eval (RedTrace.shiftPoint t x) φ = 0` on the trace `t` the
  bits are read off: `φ` vanishes at the shifted real-log point `a + (x + 1)·b`, the form
  Schwartz–Zippel bounds. -/
  szBit : Bool

/-- **Reduction analysis experiment.** Samples the challenge exponent `x`, runs `redTrace`
at the genuine powers `X = x·gen`, `X' = x²·gen`, `X'' = x³·gen`, and returns the `RedBits`:
- `winBit` reconstructs `sk = (a₀+x·b₀, aᵣ+x·bᵣ, a₁+x·b₁)` from the masks and `x` and applies the
  *real* μCMZ win predicate (consistency ∧ freshness ∧ `verify`);
- `recBit` is the reduction's extraction success `recoverDlog gen X ψ = x` on the trace's `ψ`;
- `badBit = decide (φ ≠ 0 ∧ ψ = 0)` is the Schwartz–Zippel bad event;
- `szBit = decide (φ ≠ 0 ∧ eval (t.shiftPoint x) φ = 0)` is the shift event at the trace's
  affine masks.

`Pr[recBit]` is `microCMZ3DLReductionAdv` (`redFull_recBit_eq`). -/
noncomputable def redFull (A : AGMUFAdversary F G 1) : ProbComp RedBits := do
  let x ← $ᵗ F
  let X := x • gen
  let t ← redTrace gen X (x ^ 2 • gen) (x ^ 3 • gen) A
  -- the key the masks embed at the challenge exponent, and the real win predicate on it
  let sk := maskedKey x t.aM t.bM
  let consistent := t.ρU.evalAt gen t.ep t.log.tags = t.σStar.1 ∧
    t.ρV.evalAt gen t.ep t.log.tags = t.σStar.2
  let fresh := t.mStar ∉ t.log.map (·.msg)
  pure ⟨decide consistent && decide fresh && verify sk t.mStar t.σStar,
        decide (recoverDlog gen X t.psi = x),
        decide (t.verifPoly ≠ 0 ∧ t.psi = 0),
        decide (t.verifPoly ≠ 0 ∧ MvPolynomial.eval (t.shiftPoint x) t.verifPoly = 0)⟩

/-! ## Schwartz–Zippel bad-event probability (distribution layer)

The bad-event probability `Pr[badBit | redFull A] = Pr[φ ≠ 0 ∧ ψ = 0]` is bounded by `3/p`
in two steps.

1. **Shift (deterministic).** `ψ = affineSubst a b φ = 0` forces `φ` to vanish at the *shifted*
   real-log point `w v := a v + (x+1)·b v = (a v + x·b v) + b v = θ v + b v`
   (`eval_shift_eq_zero_of_affineSubst_eq_zero`). So `badBit ⟹ szBit` where
   `szBit := decide (φ ≠ 0 ∧ MvPolynomial.eval (fun v => a v + (x+1)·b v) φ = 0)`.

2. **Schwartz–Zippel over the shear (distributional, the keystone).** Under the change of
   variables `(a v, b v) ↦ (θ v := a v + x·b v, b v)` — a uniform-preserving bijection on `F²`
   for each fixed challenge `x` (for the 4 fixed mask pairs *and* the per-query `(auⱼ, buⱼ)` pairs
   sampled inside `simulateQ`'s `sign` branch) — the entire view A sees (`H, X₀, Xᵣ, X₁`, every
   `Uⱼ, Vⱼ`) and hence `φ`, `θ` depend only on the `θ`-masks, while the `b`-masks are uniform and
   independent. Therefore the point `w = θ + b` is uniform over `Var L.length → F` independent of
   `(φ, θ)`, and `card_filter_eval_eq_zero_le` (Schwartz–Zippel, cardinality form) gives
   `Pr[szBit] ≤ 3 / |F|`.

`redFull` exposes both `badBit` and `szBit`, so the two steps compose as events on one run. -/

end KVAC.Schemes.MicroCMZ
