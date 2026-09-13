/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.RedFull

/-!
# μCMZ AGM unforgeability, `n = 1` — the Lemma 5.4 target statement (O24 §5.3)

This file states the `n = 1` advantage bound the whole `AGMReduction/`
subdirectory exists to prove:

  `AGM_UF_CMVAAdv gen A secParam ≤ microCMZ3DLReductionAdv gen A + 3/p`.

The bound speaks of the instrumented AGM game `AGM_UF_CMVAGame` of
`AlgebraicMAC.lean`; the bridge to the plain `UF_CMVAGame` is tracked in #81.

The statement is deliberately added first so that every part of the reduction
(`Core`, `Coupling`, `SignCoupling`, `RedFull`, and the parts still to be added)
reviews against a visible target. The theorem below is *assembled* (sorry-free: event
split, union bound, marginal bookkeeping) over five named sub-lemmas about the
experiment `redFull` of `AGMReduction/RedFull.lean`, of which `redFull_recBit_eq` is
proven here:

- `redFull_recBit_eq` — `redFull`'s `recBit` marginal *is* the 3-DL
  advantage: both experiments are `redTrace` at the challenge powers;
- `redFull_badBit_of_winBit_of_not_recBit` — win ∧ ¬extract forces the
  Schwartz–Zippel bad event;
- `redFull_badBit_le_szBit` — the bad event implies the shift
  event (via `Coupling`'s shift lemma);
- `redFull_szBit_le` — the shift event has probability ≤ `3/p`
  (the Schwartz–Zippel keystone);
- `AGM_UF_CMVAGame_evalDist_eq` — the real game and `redFull`'s `winBit`
  are identically distributed.

Until the remaining sub-lemmas are discharged, this subtree's `sorry`s are
exactly the four unproven ones above, and the theorem's blueprint node
(`single_attribute_mac`) shows "contains sorry".

**Two departures from O24's printed bound** (Lemma 5.4, p. 36, states
`Adv^{3-dl} + Adv^{dl} + 1/p`):

- The bad-event bound is `3/p`, not the `1/p` O24 prints
  (`docs/DESIGN_ALTERNATIVES.md`): Schwartz–Zippel hits the verification
  polynomial `φ` itself, of total degree `≤ 3`, at a shifted real-log point — see
  *The bad-event bound* below.
- The `Adv^dl` summand is dropped, on the proof of Lemma 5.4 itself (pp. 36–38):
  it builds one reduction, to 3-DL, and no DL reduction, so the summand is left
  unjustified — in O24 it survives only as nonnegative slack
  (`docs/presentations/rolf-status/errata.md` §2). Lemma 5.5's gap-DL term is
  *not* this term: it is a separate `n = poly` argument (its case (i) collision
  branch, via Thm 5.6), and there is no collision branch at `n = 1` (errata §6).
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/-! ## Sub-lemmas -/

/-- **Keygen + oracle reparametrization.** The real UF-CMVA game and `redFull`'s `winBit`
marginal are *identically distributed*: the reduction's masks make the embedded public elements
(`H, X₀, Xᵣ, X₁`) and every issued tag uniform exactly as in the real game, the reconstructed
secret `sk = (a₀+x·b₀, aᵣ+x·bᵣ, a₁+x·b₁)` plays the role of the real key, and the simulated oracle
reproduces the honest oracle's observable behaviour.

Discharged by coupling `reductionOracleImpl` (`Core.lean`) against `agmOracleImpl`
(`AlgebraicMAC.lean`) under the state invariant `redLogHonestInv` (`Coupling.lean`),
after the uniform-preserving keygen shear `(a, b) ↦ (a + x·b, b)`: the `sign` arm
through `sign_masked_tag_dist_eq` (`SignMask.lean`, whose module doc records why the
mask sample is kept opaque there), the `verify`/`help` arms through
`represented_value_eq_affineSubst_eval` (`SignCoupling.lean`). -/
lemma AGM_UF_CMVAGame_evalDist_eq (A : AGMUFAdversary F G 1) :
    evalDist (AGM_UF_CMVAGame gen secParam A)
      = evalDist ((fun t : RedBits => t.winBit) <$> redFull gen A) := by
  sorry

/-- **Extraction marginal.** `redFull`'s `recBit` is distributed as
`microCMZ3DLReductionExp gen A`: both are `redTrace` under `qdlogExp`'s challenge
powers `(x·g, x²·g, x³·g)`, so the marginal probability *is* the 3-DL advantage. -/
lemma redFull_recBit_eq (A : AGMUFAdversary F G 1) :
    Pr[(fun t : RedBits => t.recBit = true) | redFull gen A]
      = microCMZ3DLReductionAdv gen A := by
  have hmap : (fun t : RedBits => t.recBit) <$> redFull gen A
      = microCMZ3DLReductionExp gen A := by
    simp only [redFull, microCMZ3DLReductionExp, qdlogExp, microCMZ3DLReduction, map_bind,
      map_pure, bind_assoc, pure_bind, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd,
      pow_one]
  rw [microCMZ3DLReductionAdv, ← probEvent_eq_eq_probOutput, ← hmap, probEvent_map]; rfl

/-- **Win without extraction forces the bad event (deterministic core).** On
`redFull`'s support, `winBit = true` (the real `verify`/consistency/freshness on
`sk = maskedKey x t.aM t.bM`) together with `recBit ≠ true` (`recoverDlog gen X ψ ≠ x`)
forces the Schwartz–Zippel bad event `badBit = true`, i.e. `φ ≠ 0 ∧ ψ = 0` for
`φ := t.verifPoly` and `ψ := t.psi = t.log.maskedSubst t.aM t.bM φ`. The proof destructures
`redTrace`'s support once (`mem_support_bind_iff`), reads the logged tags through
`redLog_honest` + `redLog_U_form` via `redLog_transcript_facts`, then composes
`verifPoly_eval_eq_zero_of_keySmul` + `gamePoint_eq_embed_affine` (`eval (a + x·b) φ = 0`)
with the two contrapositives: `agm_n1_identity_Ustar_eq_zero` (`φ ≠ 0`, via `σ.1 ≠ 0`) and
`recoverDlog_verifPoly_eq` (`ψ = 0`, via `recoverDlog ≠ x`). -/
lemma redFull_badBit_of_winBit_of_not_recBit (A : AGMUFAdversary F G 1) (t : RedBits)
    (ht : t ∈ support (redFull gen A)) (hw : t.winBit = true) (hr : t.recBit ≠ true) :
    t.badBit = true := by
  sorry

/-! ### The bad-event bound

`Pr[badBit] = Pr[φ ≠ 0 ∧ ψ = 0]` is bounded by `3/p` in two steps on one run of `redFull`.

1. **Shift (deterministic).** `ψ = t.log.maskedSubst t.aM t.bM φ = 0` forces `φ` to vanish at
   `t.shiftPoint x = a + (x+1)·b` (`eval_shift_eq_zero_of_affineSubst_eq_zero`), so
   `badBit ⟹ szBit`.
2. **The adaptive Schwartz–Zippel bound over the shear.** Under `(a v, b v) ↦ (a v + x·b v, b v)` —
   a uniform-preserving bijection on `F²` per variable, for the four fixed mask pairs and the
   per-query `(auⱼ, buⱼ)` — A's view and hence `φ` depend only on the sheared masks while the
   `b`-masks stay uniform and independent; `t.shiftPoint x` is then uniform over
   `Var t.log.length → F` independent of `φ`, and `probEvent_eval_shift_eq_zero_le`
   (total degree `≤ 3`) gives `Pr[szBit] ≤ 3/p`. -/

/-- **Shift implication.** `badBit ⟹ szBit` pointwise on the support (step 1 above), hence
`Pr[badBit] ≤ Pr[szBit]`. -/
lemma redFull_badBit_le_szBit (A : AGMUFAdversary F G 1) :
    Pr[(fun t : RedBits => t.badBit = true) | redFull gen A]
      ≤ Pr[(fun t : RedBits => t.szBit = true) | redFull gen A] := by
  sorry

/-- **The adaptive Schwartz–Zippel bound.** `Pr[szBit] ≤ 3/p` by the shear coupling (step 2 above). -/
lemma redFull_szBit_le (A : AGMUFAdversary F G 1) :
    Pr[(fun t : RedBits => t.szBit = true) | redFull gen A]
      ≤ 3 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  sorry

/-! ## Lemma 5.4 -/

/--
**O24 Lemma 5.4, `n = 1`**. Bounds the AGM advantage by the
3-DL term plus `3/p`, with the `dlogAdv` term dropped (slack for `n = 1`).
(O24 prints `1/p`; the bad event is Schwartz–Zippel on the degree-≤3
verification polynomial, so the provable constant is `3/p` — see the module
docstring.)

**The embedding (O24 Eqs. 13–14), made precise.** Each secret exponent is a
*linear* form in the 3-DL challenge exponent `x`: the reduction samples masks
`a v, b v ←$ F` for every variable `v ∈ {η, x₀, xᵣ, x₁, u₁, …, u_q}` and sets the
real discrete log of `v` to `a v + x · b v`. These masks are *exactly* the
`affineSubst a b` masks. The public elements then follow by substitution, read
off the 3-DL powers `(X, X', X'') = (x·g, x²·g, x³·g)`:

- `H = a η · g + b η · X` (so `log_g H = a η + x · b η`);
- `Xᵣ = a xᵣ · g + b xᵣ · X`,  `X₁ = a x₁ · g + b x₁ · X`;
- `X₀ = x₀ · H = (a x₀ · a η)·g + (a x₀ · b η + b x₀ · a η)·X + (b x₀ · b η)·X'`
  (degree 2 — the corrected Eq. 13 coefficient is `a₀bₕ + b₀aₕ`);
- per Sign query `mⱼ`: sample `a uⱼ, b uⱼ`; `Uⱼ = a uⱼ · g + b uⱼ · X` and
  `Vⱼ = keyⱼ · Uⱼ` is the degree-2 element built the same way from
  `keyⱼ = x₀ + xᵣ + mⱼ x₁` (linear in `x`). Its `g`-coefficient is
  `a uⱼ · (a₀ + aᵣ + mⱼ a₁)` (= `keyⱼ · Uⱼ`); O24 Eq. 14 misprints this as
  `a uⱼ · (aₕa₀ + aₕ + mⱼ a₁)` — a *second* coefficient typo (alongside Eq. 13)
  that this code silently corrects. Verify/Help answer by evaluating the
  submitted representation (degree ≤ 3) at the powers — `X''` covers degree 3.
  (Note: O24 p. 37 calls the Verify equation degree 2; it is in fact degree 3,
  since a submitted `U` may use `X₀` or `Vⱼ`, both degree-2 in `x`, times the
  degree-1 `keyⱼ` — hence `exponentEval … X''`, not just `X, X'`.)

**Proof outline** (the assembly over the sub-lemmas above, all read on one run of
`redFull`):

1. *game bridge*: `AGM_UF_CMVAAdv gen A secParam = Pr[winBit | redFull gen A]` — the
   real game and the reduction's run are identically distributed (the masks make
   `H, X₀, Xᵣ, X₁, Uⱼ` uniform and Sign matches `mac`; blueprint `run_level_coupling`);
2. *split on extraction*: `Pr[winBit] ≤ Pr[recBit] + Pr[winBit ∧ ¬recBit]`;
3. *extraction*: `Pr[recBit] = microCMZ3DLReductionAdv gen A` (`redFull_recBit_eq`);
4. *bad event*: `winBit ∧ ¬recBit ⟹ badBit` (`redFull_badBit_of_winBit_of_not_recBit`;
   the identity branch `φ = 0` is absorbed there, since `U* = 0` contradicts `verify`'s
   `σ.1 ≠ 0`), `Pr[badBit] ≤ Pr[szBit]` (`redFull_badBit_le_szBit`), and
   `Pr[szBit] ≤ 3/p` (`redFull_szBit_le`) — *The bad-event bound* above.
-/
theorem agm_ufcmva_le_n1_explicit (A : AGMUFAdversary F G 1) :
    AGM_UF_CMVAAdv gen A secParam ≤
      microCMZ3DLReductionAdv gen A + 3 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  -- reparametrization: the AGM game's win bit is distributed as `redFull`'s `winBit`.
  have hwin_dist : AGM_UF_CMVAAdv gen A secParam
      = Pr[(fun t : RedBits => t.winBit = true) | redFull gen A] := by
    have hout : AGM_UF_CMVAAdv gen A secParam
        = Pr[= true | (fun t : RedBits => t.winBit) <$> redFull gen A] :=
      probOutput_congr rfl (AGM_UF_CMVAGame_evalDist_eq gen secParam A)
    rw [hout, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  -- Bad event ≤ 3/p: win ∧ ¬extract forces `badBit` (`redFull_badBit_of_winBit_of_not_recBit`);
  -- `badBit ⟹ szBit` (`redFull_badBit_le_szBit`); and `Pr[szBit] ≤ 3/p` (`redFull_szBit_le`).
  have hbad : Pr[(fun t : RedBits => t.winBit = true ∧ t.recBit ≠ true) | redFull gen A]
      ≤ 3 * (Fintype.card F : ℝ≥0∞)⁻¹ :=
    le_trans
      (probEvent_mono fun t ht ht' =>
        redFull_badBit_of_winBit_of_not_recBit gen A t ht ht'.1 ht'.2)
      ((redFull_badBit_le_szBit gen A).trans (redFull_szBit_le gen A))
  -- Assembly: `win ⊆ rec ∪ (win ∧ ¬rec)` (a tautology), union bound, then the
  -- extraction marginal (`redFull_recBit_eq`) rewrites `Pr[recBit]` to the 3-DL advantage.
  have hsplit : Pr[(fun t : RedBits => t.winBit = true) | redFull gen A]
      ≤ Pr[(fun t : RedBits => t.recBit = true) | redFull gen A]
        + Pr[(fun t : RedBits => t.winBit = true ∧ t.recBit ≠ true) | redFull gen A] :=
    le_trans
      (probEvent_mono fun t _ ht1 => or_iff_not_imp_left.mpr fun ht2 => ⟨ht1, ht2⟩)
      (probEvent_or_le (redFull gen A) _ _)
  rw [hwin_dist, ← redFull_recBit_eq gen A]
  exact hsplit.trans (add_le_add le_rfl hbad)

end KVAC.Schemes.MicroCMZ
