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

The statement is deliberately added first, `sorry`d, so that every part of the
reduction (`Core`, `Coupling`, `SignCoupling`, and the parts still to be added)
reviews against a visible target. The proof arrives incrementally:

1. the proof *skeleton* replaces the `sorry` here with an assembly over named
   sub-lemmas about the experiment `redFull` of `AGMReduction/RedFull.lean`;
   stated so far:
   - `redFull_recBit_eq` (proven) — `redFull`'s `recBit` marginal *is* the 3-DL
     advantage: both experiments are `redTrace` at the challenge powers;
2. each remaining sub-lemma is then discharged, sorry-free, until the theorem is
   kernel-verified with no remaining `sorry`.

Until then the theorem below carries the only `sorry` of this subtree; its
blueprint node (`single_attribute_mac`) shows "contains sorry" until proven.

**Two departures from O24's printed bound** (Lemma 5.4, p. 36, states
`Adv^{3-dl} + Adv^{dl} + 1/p`):

- The bad-event bound is `deg ψ / p ≤ 3/p` (Schwartz–Zippel on the degree-≤3
  `ψ`), not the `1/p` O24 prints (`docs/DESIGN_ALTERNATIVES.md`). With `d` the
  total degree of `φ`, the `χ^d` coefficient of `ψ` is the degree-`d`
  homogeneous part of `φ` at the `b` masks, so the bound is `d/p ≤ 3/p`, with
  equality only when `φ` has total degree 3.
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

/-! ## Lemma 5.4, non-identity branch -/

/--
**O24 Lemma 5.4, `n = 1`** (statement; the proof is assembled incrementally —
see the module docstring). Bounds the AGM advantage by the
3-DL term plus `3/p`, with the `dlogAdv` term dropped (slack for `n = 1`).
(O24 prints `1/p`; the bad event is a degree-≤3 Schwartz–Zippel restriction, so
the provable constant is `3/p` — see the module docstring.)

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

**Proof outline:**

1. rewrite `AGM_UF_CMVAAdv gen A secParam = Pr[win]` and split the win event on
   whether the forgery's verification polynomial is identically zero;
2. the identity branch is `0` by `agm_n1_identity_Ustar_eq_zero` (`U* = 0`
   contradicts `verify`'s `σ.1 ≠ 0` check) — needs the log-honesty
   invariant that every logged tag is honest;
3. the non-identity branch is `≤ qdlogAdv 3 … + 3/p`. The reduction `B₃` runs `A`
   under the simulated oracle (no `sk`; masks accumulated in the `StateT` log),
   forms `ψ = affineSubst a b (verifPoly …)`, and returns `recoverDlog g X ψ`.
   - *correctness when `ψ ≠ 0`*: `recoverDlog_verifPoly_eq` already closes this —
     verification gives `MvPolynomial.eval (fun v => a v + x·b v) (verifPoly) = 0`
     (via the `agmRepr_eval_eq_eval_toPoly` bridge), so `B₃` outputs `x`;
   - *distribution equivalence*: the simulated game is identically distributed to
     `AGM_UF_CMVAGame` (the masks make `H, X₀, Xᵣ, X₁, Uⱼ` uniform; Sign matches
     `mac`);
   - *bad event*: `ψ = 0` despite `verifPoly ≠ 0` only with probability `≤ 3/p`
     (Schwartz–Zippel over the masks: `ψ` restricts a degree-≤3 polynomial to a
     random line, so `Pr[ψ ≡ 0] ≤ deg ψ / p ≤ 3/p`). -/
theorem agm_ufcmva_le_n1_explicit (A : AGMUFAdversary F G 1) :
    AGM_UF_CMVAAdv gen A secParam ≤
      microCMZ3DLReductionAdv gen A + 3 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  sorry

end KVAC.Schemes.MicroCMZ
