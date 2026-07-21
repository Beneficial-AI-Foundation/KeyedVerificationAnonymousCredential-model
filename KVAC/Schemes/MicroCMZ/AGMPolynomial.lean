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

This is the encoding layer — the variable set, the polynomial ring, the key
polynomial `x₀ + xᵣ + m·x₁`, and the representation coefficients with their
discrete-log polynomial `toPoly`. The identity case, the affine substitution,
and the degree/root bounds build on this in later PRs of the stack.

## Setting (n = 1 attributes)

Polynomial ring `F[η, x₀, xᵣ, x₁, u₁, …, u_q]` where `η = log_G H`,
`(x₀, xᵣ, x₁)` is the MAC key, and `uⱼ = log_G Uⱼ` for the `j`-th Sign query.
An algebraic representation with coefficients `(c_g, c_h, c_0, c_r, c_1, c⃗_u,
c⃗_v)` over the transcript basis `(G, H, X₀, Xᵣ, X₁, U⃗, V⃗)` has discrete log

  `c_g + c_h·η + c_0·x₀η + c_r·xᵣ + c_1·x₁ + Σⱼ c_uⱼ·uⱼ + c_vⱼ·uⱼ·(x₀+xᵣ+mⱼx₁)`

(using `X₀ = x₀·H`, `Xᵣ = xᵣ·G`, `X₁ = x₁·G`, `Vⱼ = (x₀+xᵣ+mⱼx₁)·Uⱼ`).

The verification equation `V* = (x₀+xᵣ+m*x₁)·U*` becomes O24 Eq. 12:

  `α.toPoly · (x₀ + xᵣ + m*·x₁) = β.toPoly`.
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

end KVAC.Schemes.MicroCMZ.AGMPoly
