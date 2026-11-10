/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# A finite tape of coin bits and exact draws from `ZMod p`

O24 §3 (p. 24) writes "the length of the random coins as A.rl(λ)" for a p.p.t.
algorithm. The extractability clause of Definition 7.1 (p. 58) samples the coins
as `ρ ←$ {0, 1}^{A.rl(λ)}`. Figure 9 (p. 34) has `μCMZ.I.Usr` draw `s ←$ ℤ_p`.

This file proves that the two do not meet. A function `f` of `k` coin bits is an
algorithm with its inputs and its oracle answers fixed. For an odd prime `p` the
output of `f` on a uniform tape is not uniform on `ZMod p`. The statement is
about the unconditional distribution of the output. It places no bound on the
running time.

The report `docs/findings/FINDINGS_AND_LESSONS.md` records the finding in Part
A6.6, *Exact draws from ℤ_p and the coin tape*.
-/

namespace KVAC.Preliminaries

open Finset

/-- The counting core. For an odd prime `p`, no function from the tapes of `k`
bits to `ZMod p` has every fiber of size `2 ^ k / p`. Such a fiber size gives
`p ∣ 2 ^ k`, hence `p ∣ 2`. -/
theorem not_forall_card_fiber_mul_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℕ)
    (f : (Fin k → Bool) → ZMod p) :
    ¬ ∀ y : ZMod p, (univ.filter fun ρ => f ρ = y).card * p = 2 ^ k := by
  intro h
  have hdvd : p ∣ 2 ^ k := ⟨_, by rw [mul_comm]; exact (h 0).symm⟩
  have h2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hdvd
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

/-- For an odd prime `p`, the image of the uniform distribution on the tapes of
`k` bits under any function `f` is not the uniform distribution on `ZMod p`. -/
theorem map_uniform_bits_ne_uniform (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : ℕ)
    (f : (Fin k → Bool) → ZMod p) :
    (PMF.uniformOfFintype (Fin k → Bool)).map f ≠ PMF.uniformOfFintype (ZMod p) := by
  intro h
  apply not_forall_card_fiber_mul_eq p hp k f
  intro y
  have hy := congrArg (fun q => q y) h
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_pi, Fintype.card_bool,
    prod_const, card_univ, Fintype.card_fin, ZMod.card] at hy
  rw [tsum_fintype, ← sum_filter, sum_const, nsmul_eq_mul] at hy
  have hp0 : (p : ENNReal) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h2 : ((2 : ENNReal) ^ k) ≠ 0 := by positivity
  have h2' : ((2 : ENNReal) ^ k) ≠ ⊤ := by simp
  push_cast at hy
  have key : ((univ.filter fun ρ => y = f ρ).card : ENNReal) * p = 2 ^ k := by
    have := congrArg (fun x => x * ((2 : ENNReal) ^ k * p)) hy
    simp only at this
    rw [mul_assoc, ← mul_assoc (((2 : ENNReal) ^ k)⁻¹), ENNReal.inv_mul_cancel h2 h2', one_mul,
      mul_comm ((2 : ENNReal) ^ k) p, ← mul_assoc, ENNReal.inv_mul_cancel hp0
      (ENNReal.natCast_ne_top p), one_mul] at this
    exact this
  have : (univ.filter fun ρ => f ρ = y) = univ.filter fun ρ => y = f ρ := by
    ext; simp [eq_comm]
  rw [this]
  exact_mod_cast key

end KVAC.Preliminaries
