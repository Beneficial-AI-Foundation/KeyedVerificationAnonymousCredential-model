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
import Mathlib.Tactic.DeriveFintype

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
  deriving DecidableEq, Fintype

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

private lemma spec_keyPoly (E P0 Pr P1 : Polynomial F) (Uf : Fin q → Polynomial F)
    (m : F) :
    spec E P0 Pr P1 Uf (keyPoly m) = P0 + Pr + Polynomial.C m * P1 := by
  simp only [keyPoly, x₀, xᵣ, x₁, spec, map_add, map_mul, aeval_X, aeval_C,
    Polynomial.algebraMap_eq]

private lemma spec_toPoly (E P0 Pr P1 : Polynomial F) (Uf : Fin q → Polynomial F)
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
private lemma spec_toPoly_uZero (E P0 Pr P1 : Polynomial F) (ρ : ReprCoeffs F q)
    (msgs : Fin q → F) :
    spec E P0 Pr P1 (fun _ => 0) (ρ.toPoly msgs) =
      Polynomial.C ρ.cg + Polynomial.C ρ.ch * E +
        Polynomial.C ρ.c0 * (P0 * E) + Polynomial.C ρ.cr * Pr +
        Polynomial.C ρ.c1 * P1 := by
  rw [spec_toPoly]
  simp

/-- `spec` with `u_k ↦ U` and the other `uⱼ ↦ 0`: only the `k`-th tag term
survives. -/
private lemma spec_toPoly_uSingle (E P0 Pr P1 U : Polynomial F) (k : Fin q)
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
    -- Cross terms: `keyPoly mStar`'s `C mStar·x₁` summand is live here (x₁ ↦ X),
    -- so `α.cg` and `α.c1` each pick up an extra `·(C mStar · X^…)` copy at
    -- degrees 1 and 2. They miss degree 3, so the degree-3 read still isolates α.c1.
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
    -- Cross terms: with x₁ ↦ X² the `C mStar·x₁` summand of `keyPoly mStar`
    -- multiplies every LHS term by `C mStar`; the target `α.cu k·mStar` sits at
    -- degree 3, the `mStar`-weighted α.cg/α.c1/α.cv copies at degrees 2/4/5.
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

/-! ## The affine substitution ψ(χ) = ϕ(a + χ·b) (O24 Eqs. 13–14)

The 3-DL reduction of the non-identity case embeds its challenge by
substituting every variable with an affine form `v ↦ a_v + χ·b_v` (the masked
embedding of O24 Eqs. 13–14), turning a multivariate polynomial `ϕ` into the
univariate `ψ(χ)`. This section provides that substitution as an algebra map
and the bridge lemma relating `ψ(χ)` to `ϕ` evaluated at `v ↦ a v + χ·b v`.
The verification polynomial `ϕ` it is applied to, and the resulting degree and
root bounds, follow in the next PR of the stack. -/

/-- The affine substitution of O24 Eqs. 13–14: every variable goes to
`v ↦ a_v + χ·b_v`, the masked embedding of the 3-DL challenge. Applied to
`verifPoly` (the polynomial `ϕ`) it yields the univariate `ψ(χ)` of Eq. 16. -/
noncomputable def affineSubst (a b : Var q → F) : P F q →ₐ[F] Polynomial F :=
  aeval fun v => Polynomial.C (a v) + Polynomial.X * Polynomial.C (b v)

/-- Evaluating the affine substitution `ψ = affineSubst a b ϕ` at a scalar `χ`
recovers the multivariate evaluation of `ϕ` at the point `v ↦ a v + χ · b v`.
This is the bridge the 3-DL reduction uses: with the masks chosen so that
`a v + χ · b v` is the real discrete log of variable `v` at `χ = x` (the
challenge exponent), `ψ(x) = 0` becomes exactly the verification equation
(O24 Eq. 16). -/
lemma eval_affineSubst (a b : Var q → F) (χ : F) (ϕ : P F q) :
    Polynomial.eval χ (affineSubst a b ϕ) =
      MvPolynomial.eval (fun v => a v + χ * b v) ϕ := by
  have key : (Polynomial.aeval χ).comp (affineSubst a b) =
      MvPolynomial.aeval (fun v => a v + χ * b v) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [affineSubst, Polynomial.X_mul_C, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    Function.comp_apply, aeval_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, add_right_inj]
    ring
  have h := DFunLike.congr_fun key ϕ
  rw [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval,
    Polynomial.coe_aeval_eq_eval] at h
  exact h

/-! ## The non-identity case — degree and root bounds for ψ(χ) (O24 Eq. 16)

In the non-identity case of Lemma 5.4, the verification equation read as the
single polynomial `ϕ := α.toPoly · keyPoly m* − β.toPoly` is *nonzero*. The
3-DL reduction embeds its challenge by substituting every variable with an
affine form `v ↦ a_v + χ·b_v` (the masked embedding of O24 Eqs. 13–14),
producing the univariate partial evaluation `ψ(χ)` of Eq. 16. This section
provides the deterministic skeleton of that case:

- `deg ψ ≤ totalDegree ϕ ≤ 3` (`natDegree_affineSubst_le`,
  `totalDegree_verifPoly_le`), and
- a nonzero `ψ` has at most 3 roots in `F`
  (`card_roots_affineSubst_verifPoly_le`) — the reduction finds `log_G X`
  among them.

The probabilistic ingredient — `ψ ≠ 0` except with probability `1/p` over the
uniform masks `b` — is consumed at the game layer together with the reduction
(TODO(CMZ-M)).

**NB — the bound is `3/p`, not the `1/p` stated in O24 Eq. 16.** The paper
invokes Schwartz–Zippel to bound the bad event `ψ ≡ 0`, but for a degree-`d`
polynomial that bound is `d/p`, not `1/p`. Concretely, write
`ψ(χ) = ϕ(a + χ·b)`. Expanding, the coefficient of `χ^d` in `ψ` (with
`d = totalDegree ϕ ≤ 3`) is exactly `ϕ_d(b)` — the top-degree homogeneous part
of `ϕ` evaluated at the mask vector `b` — because only the degree-`d` monomials
of `ϕ` can reach `χ^d`, and each contributes the product of its `b`-masks.
Since `ϕ ≠ 0` we have `ϕ_d ≠ 0`, and `ψ ≡ 0 ⟹ ϕ_d(b) = 0`. As `ϕ_d` is a
nonzero polynomial of degree `d ≤ 3` in the uniform, independent masks `b`,
Schwartz–Zippel gives `Pr_b[ϕ_d(b) = 0] ≤ d/p ≤ 3/p`. The paper's `1/p` would
be correct only for a degree-1 form; the deg-3 verification polynomial needs
`3/p`. This loosens the concrete additive term (`1/p → 3/p`) but leaves the
asymptotic bound — and hence the security statement — unchanged.
-/

/-- O24 Eq. 12 as a single polynomial — the polynomial `ϕ` of the
non-identity case: the forgery's verification equation holds as a polynomial
identity iff `verifPoly … = 0`. Its affine substitution is the univariate
`ψ(χ)` of Eq. 16. -/
noncomputable def verifPoly (msgs : Fin q → F) (mStar : F)
    (α β : ReprCoeffs F q) : P F q :=
  α.toPoly msgs * keyPoly mStar - β.toPoly msgs

lemma verifPoly_eq_zero_iff (msgs : Fin q → F) (mStar : F)
    (α β : ReprCoeffs F q) :
    verifPoly msgs mStar α β = 0 ↔
      α.toPoly msgs * keyPoly mStar = β.toPoly msgs :=
  sub_eq_zero

/-- Evaluation of `verifPoly` distributes over its `α.toPoly · keyPoly − β.toPoly` structure.
Stated and proved here rather than in `AGMReduction`: distributing `MvPolynomial.eval` through
`map_sub`/`map_mul` sends instance search into a loop once an `F`-module `G` is in scope (the
`AGMReduction` import context). Here there is no such `G`, so it elaborates cleanly. -/
lemma verifPoly_eval (pt : Var q → F) (msgs : Fin q → F) (mStar : F) (α β : ReprCoeffs F q) :
    eval pt (verifPoly msgs mStar α β)
      = eval pt (α.toPoly msgs) * eval pt (keyPoly mStar) - eval pt (β.toPoly msgs) := by
  rw [verifPoly, map_sub, map_mul]

/-- `identity_case`, repackaged for the case split on `verifPoly`: if the
verification equation holds as a polynomial identity for a fresh `m*`, the
representation of `U*` is the zero polynomial. -/
theorem toPoly_eq_zero_of_verifPoly_eq_zero (msgs : Fin q → F) (mStar : F)
    (hfresh : ∀ j, mStar ≠ msgs j) (α β : ReprCoeffs F q)
    (h : verifPoly msgs mStar α β = 0) : α.toPoly msgs = 0 :=
  identity_case msgs mStar hfresh α β
    ((verifPoly_eq_zero_iff msgs mStar α β).mp h)

lemma totalDegree_keyPoly_le (m : F) : (keyPoly (q := q) m).totalDegree ≤ 1 := by
  have h1 : (x₀ + xᵣ : P F q).totalDegree ≤ 1 :=
    le_trans (totalDegree_add _ _)
      (max_le (le_of_eq (totalDegree_X _)) (le_of_eq (totalDegree_X _)))
  have h2 : (C m * x₁ : P F q).totalDegree ≤ 1 :=
    le_trans (totalDegree_mul _ _)
      (by simpa [totalDegree_C] using le_of_eq (totalDegree_X (.x1 : Var q)))
  exact le_trans (totalDegree_add _ _) (max_le h1 h2)

lemma totalDegree_toPoly_le (ρ : ReprCoeffs F q) (msgs : Fin q → F) :
    (ρ.toPoly msgs).totalDegree ≤ 2 := by
  have hC : ∀ (c : F) (p : P F q), (C c * p).totalDegree ≤ p.totalDegree :=
    fun c p => le_trans (totalDegree_mul _ _) (by simp [totalDegree_C])
  have hX : ∀ v : Var q, (X v : P F q).totalDegree ≤ 1 :=
    fun v => le_of_eq (totalDegree_X v)
  have hu : ∀ j (m : F), (u j * keyPoly m : P F q).totalDegree ≤ 2 :=
    fun j m => le_trans (totalDegree_mul _ _)
      (add_le_add (hX (.u j)) (totalDegree_keyPoly_le m))
  have hterm : ∀ j, ((C (ρ.cu j) * u j +
      C (ρ.cv j) * (u j * keyPoly (msgs j)) : P F q)).totalDegree ≤ 2 :=
    fun j => le_trans (totalDegree_add _ _)
      (max_le (le_trans (hC _ _) (le_trans (hX (.u j)) one_le_two))
        (le_trans (hC _ _) (hu j (msgs j))))
  unfold ReprCoeffs.toPoly
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
      · refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
        · refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
          · simp [totalDegree_C]
          · exact le_trans (hC _ _) (le_trans (hX .eta) one_le_two)
        · refine le_trans (hC _ _) (le_trans (totalDegree_mul _ _) ?_)
          exact add_le_add (hX .x0) (hX .eta)
      · exact le_trans (hC _ _) (le_trans (hX .xr) one_le_two)
    · exact le_trans (hC _ _) (le_trans (hX .x1) one_le_two)
  · exact le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun j _ => hterm j)

/-- `totalDegree ϕ ≤ 3` — the multivariate half of the paper's
`deg ψ ≤ totalDegree ϕ ≤ 3` bound (O24 Eq. 16); feeds
`natDegree_affineSubst_verifPoly_le`. -/
lemma totalDegree_verifPoly_le (msgs : Fin q → F) (mStar : F)
    (α β : ReprCoeffs F q) :
    (verifPoly msgs mStar α β).totalDegree ≤ 3 := by
  unfold verifPoly
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · exact le_trans (totalDegree_mul _ _)
      (add_le_add (totalDegree_toPoly_le α msgs) (totalDegree_keyPoly_le mStar))
  · exact le_trans (totalDegree_toPoly_le β msgs) (by norm_num)

/-- Substituting affine univariate forms for the variables bounds the degree
by the total degree: `deg ψ ≤ totalDegree ϕ`. -/
lemma natDegree_affineSubst_le (a b : Var q → F) (ϕ : P F q) :
    (affineSubst a b ϕ).natDegree ≤ ϕ.totalDegree := by
  have haff : ∀ v : Var q,
      (Polynomial.C (a v) + Polynomial.X * Polynomial.C (b v)).natDegree ≤ 1 :=
    fun v => le_trans (Polynomial.natDegree_add_le _ _)
      (max_le (by simp)
        (le_trans Polynomial.natDegree_mul_le (by simp)))
  conv_lhs => rw [ϕ.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [affineSubst, aeval_monomial]
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.algebraMap_eq, Polynomial.natDegree_C, zero_add, Finsupp.prod]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun v _ =>
    le_trans Polynomial.natDegree_pow_le ?_) (le_totalDegree hm)
  calc m v * (Polynomial.C (a v) + Polynomial.X * Polynomial.C (b v)).natDegree
      ≤ m v * 1 := Nat.mul_le_mul_left _ (haff v)
    _ = m v := Nat.mul_one _

/-- `deg ψ ≤ 3` for the verification polynomial (O24 Eq. 16). -/
lemma natDegree_affineSubst_verifPoly_le (a b : Var q → F)
    (msgs : Fin q → F) (mStar : F) (α β : ReprCoeffs F q) :
    (affineSubst a b (verifPoly msgs mStar α β)).natDegree ≤ 3 :=
  le_trans (natDegree_affineSubst_le a b _)
    (totalDegree_verifPoly_le msgs mStar α β)

/-- A nonzero `ψ(χ)` has at most 3 roots in `F` — the root-finding bound of
the Lemma 5.4 reduction (the discrete log of the 3-DL challenge is among the
roots, so the reduction succeeds after at most 3 candidate checks). -/
lemma card_roots_affineSubst_verifPoly_le [Fintype F] [DecidableEq F]
    (a b : Var q → F) (msgs : Fin q → F) (mStar : F) (α β : ReprCoeffs F q)
    (hne : affineSubst a b (verifPoly msgs mStar α β) ≠ 0) :
    ((Finset.univ : Finset F).filter fun χ =>
      Polynomial.eval χ (affineSubst a b (verifPoly msgs mStar α β)) = 0).card
        ≤ 3 := by
  refine le_trans (Polynomial.card_le_degree_of_subset_roots fun χ hχ => ?_)
    (natDegree_affineSubst_verifPoly_le a b msgs mStar α β)
  rw [Finset.mem_val, Finset.mem_filter] at hχ
  rw [Polynomial.mem_roots hne]
  exact hχ.2

end KVAC.Schemes.MicroCMZ.AGMPoly
