/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-!
# μCMZ AGM verification polynomial — Eq. 12 encoding (O24 §5.3, Lemma 5.4)

The pure-algebra layer of the Lemma 5.4 proof, self-contained over Mathlib
(no VCVio / game imports): the μCMZ verification equation for an algebraic
forgery, read as a polynomial identity in the secret exponents (O24 Eq. 12).

This layer adds the **identity case** of the case analysis — if the equation
holds *as polynomials* and the forged message is fresh, then the representation
of `U*` is the zero polynomial (so `U* = 0`, contradicting MAC verification; the
contradiction is derived at the game layer). The affine substitution and the
degree/root bounds build on this in later PRs of the stack.

## Setting (n = 1 attributes)

Polynomial ring `F[η, x₀, xᵣ, x₁, u₁, …, u_q]` where `η = log_G H`,
`(x₀, xᵣ, x₁)` is the MAC key, and `uⱼ = log_G Uⱼ` for the `j`-th Sign query.
An algebraic representation with coefficients `(c_g, c_h, c_0, c_r, c_1, c⃗_u,
c⃗_v)` over the transcript basis `(G, H, X₀, Xᵣ, X₁, U⃗, V⃗)` has discrete log

  `c_g + c_h·η + c_0·x₀η + c_r·xᵣ + c_1·x₁ + Σⱼ c_uⱼ·uⱼ + c_vⱼ·uⱼ·(x₀+xᵣ+mⱼx₁)`

(using `X₀ = x₀·H`, `Xᵣ = xᵣ·G`, `X₁ = x₁·G`, `Vⱼ = (x₀+xᵣ+mⱼx₁)·Uⱼ`).

The verification equation `V* = (x₀+xᵣ+m*x₁)·U*` becomes O24 Eq. 12:

  `α.toPoly · (x₀ + xᵣ + m*·x₁) = β.toPoly`.

## Proof technique: univariate power separation

Coefficient matching on `MvPolynomial` directly requires heavy `Finsupp`
monomial bookkeeping. Instead, each coefficient claim is extracted by
specializing the identity through an algebra map `F[η,x₀,xᵣ,x₁,u⃗] →ₐ F[X]`
(`spec`), assigning the two or three variables relevant to the claim distinct
powers of `X` (and `0` to the rest) so that the target coefficient lands on a
degree occupied by nothing else, then reading off a `Polynomial.coeff`. The
monomials chosen per claim follow O24's proof of Lemma 5.4:

| claim | assignment | degree read |
|---|---|---|
| `α.cg = 0` | `x₀ ↦ X` | 1 |
| `α.cr = 0` | `xᵣ ↦ X` | 2 |
| `α.ch = 0` | `η ↦ X, xᵣ ↦ X²` | 3 |
| `α.c0 = 0` | `η ↦ X², x₀ ↦ X` | 4 |
| `α.c1 = 0` | `x₁ ↦ X, x₀ ↦ X²` | 3 |
| `α.cv k = 0`, `α.cu k = β.cv k` | `u_k ↦ X, x₀ ↦ X²` | 5, 3 |
| `m*·α.cu k = m_k·β.cv k` | `u_k ↦ X, x₁ ↦ X²` | 3 |

Freshness `m* ≠ m_k` then forces `α.cu k = 0`, so `α.toPoly = 0`.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ.AGMPoly

open MvPolynomial

/-- Variables of the AGM verification polynomial for `n = 1` (O24 Eq. 12):
`η = log_G H`, the key components `x₀, xᵣ, x₁`, and `uⱼ = log_G Uⱼ` per Sign
query. -/
inductive Var (q : ℕ) : Type where
  | eta : Var q
  | x0 : Var q
  | xr : Var q
  | x1 : Var q
  | u : Fin q → Var q
  deriving DecidableEq

/-- `Var q` is equivalent to `Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Fin q` (the four
fixed variables `η, x₀, xᵣ, x₁` plus the `q` tag variables `uⱼ`); used to give it
a `Fintype` instance (needed for Schwartz–Zippel over `Var q → F`). -/
def varEquivSum (q : ℕ) : Var q ≃ Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Fin q where
  toFun
    | .eta => .inl ()
    | .x0 => .inr (.inl ())
    | .xr => .inr (.inr (.inl ()))
    | .x1 => .inr (.inr (.inr (.inl ())))
    | .u j => .inr (.inr (.inr (.inr j)))
  invFun
    | .inl _ => .eta
    | .inr (.inl _) => .x0
    | .inr (.inr (.inl _)) => .xr
    | .inr (.inr (.inr (.inl _))) => .x1
    | .inr (.inr (.inr (.inr j))) => .u j
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro (_ | _ | _ | _ | _) <;> rfl

instance instFintypeVar (q : ℕ) : Fintype (Var q) :=
  Fintype.ofEquiv _ (varEquivSum q).symm

variable {F : Type} [Field F] {q : ℕ}

/-- The polynomial ring `F[η, x₀, xᵣ, x₁, u⃗]`. -/
abbrev P (F : Type) [CommSemiring F] (q : ℕ) := MvPolynomial (Var q) F

/-- `η = log_G H`. -/
noncomputable def η : P F q := X .eta
/-- The key component `x₀`. -/
noncomputable def x₀ : P F q := X .x0
/-- The key component `xᵣ`. -/
noncomputable def xᵣ : P F q := X .xr
/-- The key component `x₁`. -/
noncomputable def x₁ : P F q := X .x1
/-- `uⱼ = log_G Uⱼ`, the exponent of the `j`-th issued tag. -/
noncomputable def u (j : Fin q) : P F q := X (.u j)

/-- The "key polynomial" `x₀ + xᵣ + m·x₁`: the μCMZ MAC scalar for a message
`m` as a polynomial in the secret key — the verification relation
`V = (x₀+xᵣ+m·x₁)·U` of O24 §5.1 (Figure 9), and the multiplier on both sides
of Eq. 12.

`C m` is the constant-polynomial embedding of the scalar `m : F` into the ring
`P F q` (equal to `m • x₁`); it is what realizes the informal `m·x₁`. The bare
field scalar `m` cannot be multiplied against the indeterminate `x₁` with ring
`*`, so it is first lifted into the polynomial ring via `MvPolynomial.C`. -/
noncomputable def keyPoly (m : F) : P F q := x₀ + xᵣ + C m * x₁

/-- The coefficients of an algebraic representation (the paper's `α⃗` or `β⃗`
of O24 Eq. 12) over the `n = 1` transcript basis
`(G, H, X₀, Xᵣ, X₁, U₁…U_q, V₁…V_q)`. This is the polynomial-layer mirror of
the game-layer structure `AGMRepr F 1`; that structure and the glue between
the two are introduced in a later PR. -/
structure ReprCoeffs (F : Type) (q : ℕ) where
  /-- Coefficient of `G` (the generator). -/
  cg : F
  /-- Coefficient of `H`. -/
  ch : F
  /-- Coefficient of `X₀ = x₀·H`. -/
  c0 : F
  /-- Coefficient of `Xᵣ = xᵣ·G`. -/
  cr : F
  /-- Coefficient of `X₁ = x₁·G`. -/
  c1 : F
  /-- Coefficients of the `Uⱼ`. -/
  cu : Fin q → F
  /-- Coefficients of the `Vⱼ = (x₀+xᵣ+mⱼx₁)·Uⱼ`. -/
  cv : Fin q → F

/-- The discrete log (base `G`) of the represented group element, as a
polynomial in the secret exponents, given the messages `mⱼ` of the Sign
queries. This is one side of O24 Eq. 12: `α.toPoly` and `β.toPoly` are the
two algebraic-representation exponents whose equality — after multiplying
`α`'s by `keyPoly m*` — is the verification equation. -/
noncomputable def ReprCoeffs.toPoly (ρ : ReprCoeffs F q) (msgs : Fin q → F) :
    P F q :=
  C ρ.cg + C ρ.ch * η + C ρ.c0 * (x₀ * η) + C ρ.cr * xᵣ + C ρ.c1 * x₁ +
    ∑ j, (C (ρ.cu j) * u j + C (ρ.cv j) * (u j * keyPoly (msgs j)))

/-! ## Univariate specializations -/

/-- The specialization `F[η,x₀,xᵣ,x₁,u⃗] →ₐ F[X]` sending the five variable
groups to the given univariate polynomials. -/
noncomputable def spec (E P0 Pr P1 : Polynomial F) (Uf : Fin q → Polynomial F) :
    P F q →ₐ[F] Polynomial F :=
  aeval fun v : Var q => match v with
    | Var.eta => E
    | Var.x0 => P0
    | Var.xr => Pr
    | Var.x1 => P1
    | Var.u j => Uf j

lemma spec_keyPoly (E P0 Pr P1 : Polynomial F) (Uf : Fin q → Polynomial F)
    (m : F) :
    spec E P0 Pr P1 Uf (keyPoly m) = P0 + Pr + Polynomial.C m * P1 := by
  simp only [keyPoly, x₀, xᵣ, x₁, spec, map_add, map_mul, aeval_X, aeval_C,
    Polynomial.algebraMap_eq]

lemma spec_toPoly (E P0 Pr P1 : Polynomial F) (Uf : Fin q → Polynomial F)
    (ρ : ReprCoeffs F q) (msgs : Fin q → F) :
    spec E P0 Pr P1 Uf (ρ.toPoly msgs) =
      Polynomial.C ρ.cg + Polynomial.C ρ.ch * E +
        Polynomial.C ρ.c0 * (P0 * E) + Polynomial.C ρ.cr * Pr +
        Polynomial.C ρ.c1 * P1 +
        ∑ j, (Polynomial.C (ρ.cu j) * Uf j +
          Polynomial.C (ρ.cv j) *
            (Uf j * (P0 + Pr + Polynomial.C (msgs j) * P1))) := by
  simp only [ReprCoeffs.toPoly, keyPoly, η, x₀, xᵣ, x₁, u, spec, map_add,
    map_mul, map_sum, aeval_X, aeval_C, Polynomial.algebraMap_eq]

/-- `MvPolynomial.eval` of `toPoly` at a point `pt`, expanded — the base-ring
analog of `spec_toPoly`. Used by the game-layer eval bridge to turn a
representation's group evaluation into its `toPoly` evaluated at the
transcript's discrete-log point. -/
lemma ReprCoeffs.eval_toPoly (pt : Var q → F) (ρ : ReprCoeffs F q) (msgs : Fin q → F) :
    eval pt (ρ.toPoly msgs)
      = ρ.cg + ρ.ch * pt .eta + ρ.c0 * (pt .x0 * pt .eta) + ρ.cr * pt .xr + ρ.c1 * pt .x1
        + ∑ j, (ρ.cu j * pt (.u j)
            + ρ.cv j * (pt (.u j) * (pt .x0 + pt .xr + msgs j * pt .x1))) := by
  simp only [ReprCoeffs.toPoly, keyPoly, η, x₀, xᵣ, x₁, u, map_add, map_mul, map_sum,
    eval_C, eval_X]

/-- `spec` with all `uⱼ ↦ 0`: the tag terms vanish. -/
lemma spec_toPoly_uZero (E P0 Pr P1 : Polynomial F) (ρ : ReprCoeffs F q)
    (msgs : Fin q → F) :
    spec E P0 Pr P1 (fun _ => 0) (ρ.toPoly msgs) =
      Polynomial.C ρ.cg + Polynomial.C ρ.ch * E +
        Polynomial.C ρ.c0 * (P0 * E) + Polynomial.C ρ.cr * Pr +
        Polynomial.C ρ.c1 * P1 := by
  rw [spec_toPoly]
  simp

/-- `spec` with `u_k ↦ U` and the other `uⱼ ↦ 0`: only the `k`-th tag term
survives. -/
lemma spec_toPoly_uSingle (E P0 Pr P1 U : Polynomial F) (k : Fin q)
    (ρ : ReprCoeffs F q) (msgs : Fin q → F) :
    spec E P0 Pr P1 (fun j => if j = k then U else 0) (ρ.toPoly msgs) =
      Polynomial.C ρ.cg + Polynomial.C ρ.ch * E +
        Polynomial.C ρ.c0 * (P0 * E) + Polynomial.C ρ.cr * Pr +
        Polynomial.C ρ.c1 * P1 +
        (Polynomial.C (ρ.cu k) * U + Polynomial.C (ρ.cv k) *
          (U * (P0 + Pr + Polynomial.C (msgs k) * P1))) := by
  rw [spec_toPoly]
  congr 1
  rw [Finset.sum_add_distrib]
  simp [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq']

/--
**Identity case of O24 Lemma 5.4** (Eq. 12 over the polynomial ring): if the
verification equation of an algebraic forgery for a *fresh* message `m*` holds
as a polynomial identity, then the representation of `U*` is the zero
polynomial.

At the game layer this is a contradiction: MAC verification requires
`U* ≠ 0`, while a zero polynomial evaluates (at the real discrete logs) to
`U* = 0`. Hence a winning forgery must fall into the non-identity case, where
the 3-DL reduction applies.
-/
theorem identity_case (msgs : Fin q → F) (mStar : F)
    (hfresh : ∀ j, mStar ≠ msgs j) (α β : ReprCoeffs F q)
    (hid : α.toPoly msgs * keyPoly mStar = β.toPoly msgs) :
    α.toPoly msgs = 0 := by
  -- The per-claim pattern: specialize `hid` through `spec` (power-separating
  -- assignment), normalize the resulting univariate identity into an explicit
  -- canonical form with `linear_combination`, and read off one coefficient.
  -- α.cg = 0, via x₀ ↦ X, degree 1
  have hcg : α.cg = 0 := by
    have h := DFunLike.congr_arg
      (spec (0 : Polynomial F) (Polynomial.X ^ 1) 0 0 (fun _ => 0)) hid
    rw [map_mul, spec_toPoly_uZero, spec_toPoly_uZero, spec_keyPoly] at h
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 1 =
        (Polynomial.C β.cg : Polynomial F) := by linear_combination h
    have h3 := congrArg (fun p => Polynomial.coeff p 1) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  -- α.cr = 0, via xᵣ ↦ X, degree 2
  have hcr : α.cr = 0 := by
    have h := DFunLike.congr_arg
      (spec (0 : Polynomial F) 0 (Polynomial.X ^ 1) 0 (fun _ => 0)) hid
    rw [map_mul, spec_toPoly_uZero, spec_toPoly_uZero, spec_keyPoly] at h
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 1 +
          Polynomial.C α.cr * Polynomial.X ^ 2 =
        Polynomial.C β.cg + Polynomial.C β.cr * Polynomial.X ^ 1 := by
      linear_combination h
    have h3 := congrArg (fun p => Polynomial.coeff p 2) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  -- α.ch = 0, via η ↦ X, xᵣ ↦ X², degree 3
  have hch : α.ch = 0 := by
    have h := DFunLike.congr_arg
      (spec (Polynomial.X ^ 1) 0 (Polynomial.X ^ 2) 0 (fun _ => 0)) hid
    rw [map_mul, spec_toPoly_uZero, spec_toPoly_uZero, spec_keyPoly] at h
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 2 +
          Polynomial.C α.ch * Polynomial.X ^ 3 +
          Polynomial.C α.cr * Polynomial.X ^ 4 =
        Polynomial.C β.cg + Polynomial.C β.ch * Polynomial.X ^ 1 +
          Polynomial.C β.cr * Polynomial.X ^ 2 := by
      linear_combination h
    have h3 := congrArg (fun p => Polynomial.coeff p 3) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  -- α.c0 = 0, via η ↦ X², x₀ ↦ X, degree 4
  have hc0 : α.c0 = 0 := by
    have h := DFunLike.congr_arg
      (spec (Polynomial.X ^ 2) (Polynomial.X ^ 1) 0 0 (fun _ => 0)) hid
    rw [map_mul, spec_toPoly_uZero, spec_toPoly_uZero, spec_keyPoly] at h
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 1 +
          Polynomial.C α.ch * Polynomial.X ^ 3 +
          Polynomial.C α.c0 * Polynomial.X ^ 4 =
        Polynomial.C β.cg + Polynomial.C β.ch * Polynomial.X ^ 2 +
          Polynomial.C β.c0 * Polynomial.X ^ 3 := by
      linear_combination h
    have h3 := congrArg (fun p => Polynomial.coeff p 4) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  -- α.c1 = 0, via x₁ ↦ X, x₀ ↦ X², degree 3
  have hc1 : α.c1 = 0 := by
    have h := DFunLike.congr_arg
      (spec (0 : Polynomial F) (Polynomial.X ^ 2) 0 (Polynomial.X ^ 1)
        (fun _ => 0)) hid
    rw [map_mul, spec_toPoly_uZero, spec_toPoly_uZero, spec_keyPoly] at h
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 2 +
          Polynomial.C α.cg * (Polynomial.C mStar * Polynomial.X ^ 1) +
          Polynomial.C α.c1 * Polynomial.X ^ 3 +
          Polynomial.C α.c1 * (Polynomial.C mStar * Polynomial.X ^ 2) =
        Polynomial.C β.cg + Polynomial.C β.c1 * Polynomial.X ^ 1 := by
      linear_combination h
    have h3 := congrArg (fun p => Polynomial.coeff p 3) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_C] using h3
  -- α.cv k = 0 (degree 5) and α.cu k = β.cv k (degree 3), via u_k ↦ X, x₀ ↦ X²
  have huSingle : ∀ k,
      Polynomial.C α.cg * Polynomial.X ^ 2 +
        Polynomial.C (α.cu k) * Polynomial.X ^ 3 +
        Polynomial.C (α.cv k) * Polynomial.X ^ 5 =
      Polynomial.C β.cg + Polynomial.C (β.cu k) * Polynomial.X ^ 1 +
        Polynomial.C (β.cv k) * Polynomial.X ^ 3 := by
    intro k
    have h := DFunLike.congr_arg
      (spec (0 : Polynomial F) (Polynomial.X ^ 2) 0 0
        (fun j => if j = k then Polynomial.X ^ 1 else 0)) hid
    rw [map_mul, spec_toPoly_uSingle, spec_toPoly_uSingle, spec_keyPoly] at h
    linear_combination h
  have hcv : ∀ k, α.cv k = 0 := by
    intro k
    have h3 := congrArg (fun p => Polynomial.coeff p 5) (huSingle k)
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  have hcu_eq : ∀ k, α.cu k = β.cv k := by
    intro k
    have h3 := congrArg (fun p => Polynomial.coeff p 3) (huSingle k)
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  -- α.cu k · m* = β.cv k · m_k, via u_k ↦ X, x₁ ↦ X², degree 3
  have hcu_m : ∀ k, α.cu k * mStar = β.cv k * msgs k := by
    intro k
    have h := DFunLike.congr_arg
      (spec (0 : Polynomial F) 0 0 (Polynomial.X ^ 2)
        (fun j => if j = k then Polynomial.X ^ 1 else 0)) hid
    rw [map_mul, spec_toPoly_uSingle, spec_toPoly_uSingle, spec_keyPoly] at h
    have h2 : Polynomial.C α.cg * (Polynomial.C mStar * Polynomial.X ^ 2) +
          Polynomial.C α.c1 * (Polynomial.C mStar * Polynomial.X ^ 4) +
          Polynomial.C (α.cu k) * (Polynomial.C mStar * Polynomial.X ^ 3) +
          Polynomial.C (α.cv k) * (Polynomial.C (msgs k) *
            (Polynomial.C mStar * Polynomial.X ^ 5)) =
        Polynomial.C β.cg + Polynomial.C β.c1 * Polynomial.X ^ 2 +
          Polynomial.C (β.cu k) * Polynomial.X ^ 1 +
          Polynomial.C (β.cv k) * (Polynomial.C (msgs k) * Polynomial.X ^ 3) := by
      linear_combination h
    have h3 := congrArg (fun p => Polynomial.coeff p 3) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_C] using h3
  -- freshness kills α.cu
  have hcu : ∀ k, α.cu k = 0 := by
    intro k
    have h := hcu_m k
    rw [hcu_eq k] at h
    have hz : (mStar - msgs k) * β.cv k = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · exact absurd (sub_eq_zero.mp h') (hfresh k)
    · rw [hcu_eq k]
      exact h'
  -- assemble: every coefficient of α is zero
  simp [ReprCoeffs.toPoly, hcg, hch, hc0, hcr, hc1, hcu, hcv]

/--
If the representation polynomial is zero, its evaluation at any point — in
particular the real discrete logs — is zero. This is the trivial direction of
the evaluation bridge (`eval` is a ring hom, so `eval 0 = 0`), and it is the
only part carried here. The game layer combines it with `U* = (α.toPoly).eval
dlogs • G` to turn `identity_case` into a contradiction with `U* ≠ 0`; the
substantive nonzero direction lives with the game.
-/
theorem eval_eq_zero_of_toPoly_eq_zero (msgs : Fin q → F)
    (α : ReprCoeffs F q) (h : α.toPoly msgs = 0) (point : Var q → F) :
    eval point (α.toPoly msgs) = 0 := by
  rw [h]; simp

end KVAC.Schemes.MicroCMZ.AGMPoly
