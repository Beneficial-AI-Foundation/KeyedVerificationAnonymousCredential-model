/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.AGMPolynomial
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# μCMZ_AT one-more unforgeability — the polynomial layer of Equations 17 to 22 (O24 §5.6)

The pure-algebra layer of the Theorem 5.11 proof at `n = 1`, over Mathlib only
(no game imports), mirroring `AGMPolynomial.lean`, the Lemma 5.4 layer it
extends: the polynomials the proof reads off an algebraic transcript, in the
ring `AGMPoly.P F r = F[η, x₀, xᵣ, x₁, u₁, …, u_r]` of that file. Track CMZ-OMUF,
step A3 of the Theorem 5.3 plan, part 17a of item 17 (issue #189), delivered
in two parts: Equations 17 and 18, the commitment polynomials, then Equation 22,
the forgery polynomial with the case split of the proof.

## Setting

- `r` is the number of blinded pairs `(U'_k, V'_k)` issued in the final
  transcript, the length of the representation basis, not the Sign budget: a
  refused Sign query issues no pair and gets no variable.
- `η = log_G H`, `xᵣ = log_G Xᵣ`, `x₁ = log_G X₁`, `u_k = log_G U'_k` for the
  `k`-th issued pair, and `x₀` the sampled key component with `X₀ = x₀·H` (the
  paper writes `log_H X₀`, which does not determine `x₀` when `H = 0`), as in the
  MAC layer's `gamePoint`.
- The server answers a commitment `C'` with `U' = u·G` and
  `V' = x₀·U' + u·(C' + Xᵣ) = u·(x₀ + xᵣ + c)·G`, `c` the exponent of `C'`. So
  the `V'_k` basis element has exponent `u_k·(x₀ + xᵣ + c_k)`, with `c_k` the
  polynomial of the `k`-th issued commitment (Equation 18). This is the one
  difference from the MAC layer, where `V_j = (x₀ + xᵣ + m_j·x₁)·U_j` and
  `ReprCoeffs.toPoly` takes the messages `m_j` instead of the polynomials `c_k`.

## What is defined, and what uses it

  ReprCoeffs.toPolyAt γ cs          exponent of a representation γ, given the
                                    commitment polynomials cs          (Eq 17 read in the exponent)
    |     eval_toPolyAt             its evaluation at a point, in closed form
    |---> omufCommitPolys γs        c_1, …, c_r by a left fold in issuance order,
    |                               each given the earlier polynomials as arguments (Eq 18)
    |     omufCommitPolys_nil, omufCommitPolys_append_singleton, omufCommitPolys_length
    '---> omufForgeryPoly cs m* α β φ = toPolyAt α · keyPoly m* − toPolyAt β        (Eq 22)
            |
            '---> HasUMonomial φ, HasEtaMonomial φ, HasXMonomial φ
                                    the three variable groups of the case split, items (i) to (iii)
                  cases_of_mem_vars a variable of φ falls in one of the three groups

`OneMoreUnforgeability/Transcript.lean` reads these off the game transcript
(`OMUFTrace`) to define the case events that Claims 5.12 to 5.14 bound
(`Statements.lean`).

## Where the game-level facts are proved

The game-level evaluation bridge, the Equation 18 bridge announced in the
module docstring of `OneMoreUnforgeability/Game.lean`: at the discrete-log
point of an honest run, `c_k` evaluates to the logarithm of the `k`-th issued
commitment and `toPolyAt γ cs` to the
logarithm of the element `γ` represents, by induction over the transcript
through the gate and the server's honest answers, so that `φ` vanishes at that
point exactly when the verification equation `V* = (x₀ + xᵣ + m*·x₁)·U*` holds
(acceptance also needs `U* ≠ 0`, so a verifying forgery has vanishing `φ`, not
conversely). `eval_toPolyAt` is its algebraic half; the induction over the run
is `OMUFTrace.eval_point_cs` in `Bridge.lean`. The coefficient identities of
Equations 20 and 21 are `forgeryPoly_eq_zero_coeffs` in this file. The degree
bounds and the constant audit belong to the proofs of the Claims.

## Conventions

"φ has a nonzero monomial in `v`" is Mathlib's `v ∈ φ.vars`, the variables
occurring in some monomial of `φ` with nonzero coefficient. The fold of
Equation 18 reads earlier polynomials through `List.getD … 0`, so a slot not yet
issued contributes `γ_{u,k}·u_k + γ_{v,k}·u_k·(x₀ + xᵣ)` rather than nothing;
for a representation accepted by the game's exact-length gate, the conversion
`toReprCoeffs` pads both coefficients of every not-yet-issued pair with `0`, so
the contribution is `0`. The layer itself accepts any coefficient lists, so
this triangularity is a property of gated inputs, the `hlen` of `OMUFTrace.eval_point_cs`.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ.AGMPoly

open MvPolynomial

variable {F : Type} [Field F] {r : ℕ}

/-! ## Equations 17 and 18 -/

/--
The exponent of a represented group element as a polynomial, given the
commitment polynomials `cs` of the issued pairs: O24 Equation 17 read in the
exponent, `γ_g + γ_h·η + γ_0·x₀η + γ_r·xᵣ + γ_1·x₁ + Σ_k γ_{u,k}·u_k +
γ_{v,k}·u_k·(x₀ + xᵣ + c_k)`. The counterpart for the OMUF game of
`ReprCoeffs.toPoly`, which has `m_k·x₁` where this has `c_k` (module docstring,
*Setting*).
-/
noncomputable def ReprCoeffs.toPolyAt (γ : ReprCoeffs F r) (cs : Fin r → P F r) : P F r :=
  C γ.cg + C γ.ch * η + C γ.c0 * (x₀ * η) + C γ.cr * xᵣ + C γ.c1 * x₁ +
    ∑ k, (C (γ.cu k) * u k + C (γ.cv k) * (u k * (x₀ + xᵣ + cs k)))

/-- Evaluation of `toPolyAt` at a point, in closed form: the algebraic half of
the Equation 18 bridge (module docstring, *Obligations deferred to the proof
phase*), the counterpart for the OMUF game of `ReprCoeffs.eval_toPoly`. -/
theorem ReprCoeffs.eval_toPolyAt (pt : Var r → F) (γ : ReprCoeffs F r)
    (cs : Fin r → P F r) :
    eval pt (γ.toPolyAt cs)
      = γ.cg + γ.ch * pt .eta + γ.c0 * (pt .x0 * pt .eta) + γ.cr * pt .xr + γ.c1 * pt .x1
        + ∑ k, (γ.cu k * pt (.u k)
            + γ.cv k * (pt (.u k) * (pt .x0 + pt .xr + eval pt (cs k)))) := by
  simp only [ReprCoeffs.toPolyAt, η, x₀, xᵣ, x₁, u, map_add, map_mul, map_sum, eval_C,
    eval_X]

/--
The commitment polynomials `c_1, …, c_r` of O24 Equation 18, from the
representations of the issued commitments in issuance order: a left fold in
which the `j`-th polynomial is `toPolyAt` of the `j`-th representation with the
`k`-th earlier polynomial in slot `k` and `0` in the slots not yet issued.
-/
noncomputable def omufCommitPolys (γs : List (ReprCoeffs F r)) : List (P F r) :=
  γs.foldl (fun acc γ => acc ++ [γ.toPolyAt fun k => acc.getD k 0]) []

@[simp] theorem omufCommitPolys_nil : omufCommitPolys ([] : List (ReprCoeffs F r)) = [] := rfl

/-- One more representation appends one more polynomial, given the earlier
polynomials as arguments: the fold unrolled by one step, for reasoning about the
`j`-th polynomial. -/
theorem omufCommitPolys_append_singleton (γs : List (ReprCoeffs F r)) (γ : ReprCoeffs F r) :
    omufCommitPolys (γs ++ [γ]) =
      omufCommitPolys γs ++ [γ.toPolyAt fun k => (omufCommitPolys γs).getD k 0] := by
  simp only [omufCommitPolys, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The fold issues one polynomial per representation. -/
theorem omufCommitPolys_length (γs : List (ReprCoeffs F r)) :
    (omufCommitPolys γs).length = γs.length := by
  suffices h : ∀ acc : List (P F r),
      (γs.foldl (fun acc γ => acc ++ [γ.toPolyAt fun k => acc.getD k 0]) acc).length =
        acc.length + γs.length by
    simpa using h []
  induction γs with
  | nil => intro acc; simp
  | cons γ rest ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

/-- The `j`-th commitment polynomial is `toPolyAt` of the `j`-th representation with the earlier
polynomials in the earlier slots and `0` from slot `j` on (Equation 18 read at position `j`). -/
theorem omufCommitPolys_getElem (γs : List (ReprCoeffs F r)) (j : ℕ)
    (hj : j < (omufCommitPolys γs).length) :
    (omufCommitPolys γs)[j] =
      (γs[j]'(by rwa [omufCommitPolys_length] at hj)).toPolyAt
        fun k => if (k : ℕ) < j then (omufCommitPolys γs).getD k 0 else 0 := by
  induction γs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton γs γ ih =>
    have hlen := omufCommitPolys_length γs
    have hj' : j < γs.length + 1 := by
      simpa [omufCommitPolys_append_singleton, hlen] using hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hlt | rfl
    · -- `j` is among the earlier representations
      have hj0 : j < (omufCommitPolys γs).length := by omega
      simp only [omufCommitPolys_append_singleton]
      rw [List.getElem_append_left hj0, List.getElem_append_left hlt, ih j hj0]
      congr 1
      funext k
      by_cases hk : (k : ℕ) < j
      · simp only [hk, if_true]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      · simp only [hk, if_false]
    · -- `j` is the new last representation
      simp only [omufCommitPolys_append_singleton]
      rw [List.getElem_append_right, List.getElem_append_right]
      · simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
        congr 1
        funext k
        by_cases hk : (k : ℕ) < γs.length
        · simp only [hk, if_true]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
        · simp only [hk, if_false]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          simp
      · omega
      · omega

/-! ## Equation 22 -/

/--
The forgery polynomial `φ` of O24 Equation 22 for a forgery `(m*, (U*, V*))`
with representations `α` of `U*` and `β` of `V*` over the final transcript:
`toPolyAt α · (x₀ + xᵣ + m*·x₁) − toPolyAt β`. Through the evaluation lemma of
Equation 18, which `OMUFTrace.eval_point_forgeryPoly` proves for a run, its evaluation at
the discrete logarithms of an honest run is `0` when the forgery verifies; the
pigeonhole step and the coefficient identities of Equations 20 and 21 then show
that the forgery the pigeonhole step selects, one that is not the unblinding of
any issued pair, has a nonzero `φ`, a polynomial with a root at the secret
point, which is what the three Claims exploit.
-/
noncomputable def omufForgeryPoly (cs : Fin r → P F r) (mStar : F) (α β : ReprCoeffs F r) :
    P F r :=
  α.toPolyAt cs * keyPoly mStar - β.toPolyAt cs

/-! ## The case split, items (i) to (iii) of p. 45 -/

/-- Item (i): `φ` has a nonzero monomial in some `u_j` (Claim 5.12). -/
def HasUMonomial (φ : P F r) : Prop := ∃ j : Fin r, Var.u j ∈ φ.vars

/-- Item (ii): `φ` has a nonzero monomial in `η` (Claim 5.13). -/
def HasEtaMonomial (φ : P F r) : Prop := Var.eta ∈ φ.vars

/-- Item (iii): `φ` has a nonzero monomial in `x₀`, `xᵣ` or `x₁` (Claim 5.14,
three cases). -/
def HasXMonomial (φ : P F r) : Prop :=
  Var.x0 ∈ φ.vars ∨ Var.xr ∈ φ.vars ∨ Var.x1 ∈ φ.vars

/-- The three groups exhaust the variables: any variable occurring in `φ` puts
`φ` in one of the cases. `omuf_cover` applies it to the `φ` of the forgery the
pigeonhole step selects, a nonzero polynomial vanishing at the secret point,
hence non-constant, hence with a variable. -/
theorem cases_of_mem_vars {φ : P F r} {v : Var r} (hv : v ∈ φ.vars) :
    HasUMonomial φ ∨ HasEtaMonomial φ ∨ HasXMonomial φ := by
  cases v with
  | eta => exact Or.inr (Or.inl hv)
  | x0 => exact Or.inr (Or.inr (Or.inl hv))
  | xr => exact Or.inr (Or.inr (Or.inr (Or.inl hv)))
  | x1 => exact Or.inr (Or.inr (Or.inr (Or.inr hv)))
  | u j => exact Or.inl ⟨j, hv⟩

/-! ## The `u`-free part: `ev0`

The coefficient reading of Equations 20 and 21 needs only the `u`-degree 0 and 1 parts of a
forgery polynomial. Setting every `u_k` to `0` (`ev0`), optionally after differentiating in one
`u_j`, isolates them without reading the commitment polynomials `c_k` recursively: `cs` enters
`toPolyAt` only multiplied by some `u k`. -/

/-- Sets every `u_k` to `0` and fixes `η, x₀, xᵣ, x₁`. -/
noncomputable def ev0 : P F r →ₐ[F] P F r :=
  aeval fun v => match v with
    | .u _ => 0
    | .eta => X .eta
    | .x0 => X .x0
    | .xr => X .xr
    | .x1 => X .x1

@[simp] theorem ev0_u (k : Fin r) : ev0 (u k : P F r) = 0 := by
  simp [ev0, u]

@[simp] theorem ev0_eta : ev0 (η : P F r) = η := by simp [ev0, η]
@[simp] theorem ev0_x₀ : ev0 (x₀ : P F r) = x₀ := by simp [ev0, x₀]
@[simp] theorem ev0_xᵣ : ev0 (xᵣ : P F r) = xᵣ := by simp [ev0, xᵣ]
@[simp] theorem ev0_x₁ : ev0 (x₁ : P F r) = x₁ := by simp [ev0, x₁]

/-- The `u`-free part of `toPolyAt`, whatever the commitment polynomials. -/
theorem ev0_toPolyAt (γ : ReprCoeffs F r) (cs : Fin r → P F r) :
    ev0 (γ.toPolyAt cs)
      = C γ.cg + C γ.ch * η + C γ.c0 * (x₀ * η) + C γ.cr * xᵣ + C γ.c1 * x₁ := by
  simp [ReprCoeffs.toPolyAt]

@[simp] theorem pderiv_u_eta (j : Fin r) : pderiv (Var.u j) (η : P F r) = 0 := by
  simp [η, pderiv_X]
@[simp] theorem pderiv_u_x₀ (j : Fin r) : pderiv (Var.u j) (x₀ : P F r) = 0 := by
  simp [x₀, pderiv_X]
@[simp] theorem pderiv_u_xᵣ (j : Fin r) : pderiv (Var.u j) (xᵣ : P F r) = 0 := by
  simp [xᵣ, pderiv_X]
@[simp] theorem pderiv_u_x₁ (j : Fin r) : pderiv (Var.u j) (x₁ : P F r) = 0 := by
  simp [x₁, pderiv_X]
theorem pderiv_u_u (j k : Fin r) :
    pderiv (Var.u j) (u k : P F r) = if k = j then 1 else 0 := by
  simp [u, pderiv_X, Pi.single_apply, eq_comm]

/-- The `u_j`-linear part of `toPolyAt`: differentiate in `u_j`, then set every `u` to `0`. Only
the `j`-th slot of `cs` survives, through its own `u`-free part. -/
theorem ev0_pderiv_u_toPolyAt (γ : ReprCoeffs F r) (cs : Fin r → P F r) (j : Fin r) :
    ev0 (pderiv (Var.u j) (γ.toPolyAt cs))
      = C (γ.cu j) + C (γ.cv j) * (x₀ + xᵣ + ev0 (cs j)) := by
  simp only [ReprCoeffs.toPolyAt, map_add, map_sum, Derivation.leibniz, pderiv_C,
    pderiv_u_eta, pderiv_u_x₀, pderiv_u_xᵣ, pderiv_u_x₁, pderiv_u_u]
  simp [Finset.sum_add_distrib, apply_ite ev0]

@[simp] theorem ev0_keyPoly (m : F) : ev0 (keyPoly m : P F r) = keyPoly m := by
  simp [keyPoly]

theorem pderiv_u_keyPoly (j : Fin r) (m : F) : pderiv (Var.u j) (keyPoly m : P F r) = 0 := by
  simp [keyPoly]

/-- The `u`-free part of the forgery polynomial of Equation 22. -/
theorem ev0_forgeryPoly (cs : Fin r → P F r) (m : F) (α β : ReprCoeffs F r) :
    ev0 (omufForgeryPoly cs m α β)
      = ev0 (α.toPolyAt cs) * keyPoly m - ev0 (β.toPolyAt cs) := by
  simp [omufForgeryPoly]

/-- The `u_j`-linear part of the forgery polynomial of Equation 22: `keyPoly` has no `u`, so
only the representations are differentiated. -/
theorem ev0_pderiv_u_forgeryPoly (cs : Fin r → P F r) (m : F) (α β : ReprCoeffs F r)
    (j : Fin r) :
    ev0 (pderiv (Var.u j) (omufForgeryPoly cs m α β))
      = ev0 (pderiv (Var.u j) (α.toPolyAt cs)) * keyPoly m
        - ev0 (pderiv (Var.u j) (β.toPolyAt cs)) := by
  simp [omufForgeryPoly, Derivation.leibniz, pderiv_u_keyPoly, mul_comm]

/-- The `u`-free part of a representation's exponent: `toPolyAt` with the tag coefficients
dropped (`ev0_toPolyAt`). -/
noncomputable def ReprCoeffs.uFree (γ : ReprCoeffs F r) : P F r :=
  C γ.cg + C γ.ch * η + C γ.c0 * (x₀ * η) + C γ.cr * xᵣ + C γ.c1 * x₁

/-- The `u`-free part of the `j`-th commitment polynomial (Equation 18) is that of the
`j`-th representation, whatever the earlier polynomials. -/
theorem ev0_omufCommitPolys_getElem (γs : List (ReprCoeffs F r)) (j : ℕ)
    (hj : j < (omufCommitPolys γs).length) :
    ev0 ((omufCommitPolys γs)[j]) =
      (γs[j]'(by rwa [omufCommitPolys_length] at hj)).uFree := by
  induction γs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton γs γ ih =>
    have hlen := omufCommitPolys_length γs
    have hj' : j < γs.length + 1 := by
      simpa [omufCommitPolys_append_singleton, hlen] using hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hlt | rfl
    · -- `j` is among the earlier representations
      simp only [omufCommitPolys_append_singleton]
      rw [List.getElem_append_left, List.getElem_append_left]
      exact ih j (by omega)
    · -- `j` is the new last representation
      simp only [omufCommitPolys_append_singleton]
      rw [List.getElem_append_right, List.getElem_append_right]
      · simpa using ev0_toPolyAt γ _
      · omega
      · omega

/-! ## Univariate specializations of `toPolyAt` -/

theorem spec_keyPoly' (E P0 Pr P1 : Polynomial F) (Uf : Fin r → Polynomial F) (m : F) :
    spec E P0 Pr P1 Uf (keyPoly m) = P0 + Pr + Polynomial.C m * P1 := by
  simp only [keyPoly, x₀, xᵣ, x₁, spec, map_add, map_mul, aeval_X, aeval_C,
    Polynomial.algebraMap_eq]

theorem spec_C (E P0 Pr P1 : Polynomial F) (Uf : Fin r → Polynomial F) (a : F) :
    spec E P0 Pr P1 Uf (C a) = Polynomial.C a := by
  simp [spec]

theorem spec_x₀ (E P0 Pr P1 : Polynomial F) (Uf : Fin r → Polynomial F) :
    spec E P0 Pr P1 Uf x₀ = P0 := by
  simp [spec, x₀]

theorem spec_xᵣ (E P0 Pr P1 : Polynomial F) (Uf : Fin r → Polynomial F) :
    spec E P0 Pr P1 Uf xᵣ = Pr := by
  simp [spec, xᵣ]

/-- `spec` with every `u ↦ 0`: the commitment polynomials `cs` drop out, since `toPolyAt` uses
them only multiplied by some `u k`. -/
theorem spec_toPolyAt_uZero (E P0 Pr P1 : Polynomial F) (γ : ReprCoeffs F r)
    (cs : Fin r → P F r) :
    spec E P0 Pr P1 (fun _ => 0) (γ.toPolyAt cs) =
      Polynomial.C γ.cg + Polynomial.C γ.ch * E + Polynomial.C γ.c0 * (P0 * E) +
        Polynomial.C γ.cr * Pr + Polynomial.C γ.c1 * P1 := by
  simp [ReprCoeffs.toPolyAt, spec, η, x₀, xᵣ, x₁, u]

theorem spec_uFree (E P0 Pr P1 : Polynomial F) (Uf : Fin r → Polynomial F)
    (γ : ReprCoeffs F r) :
    spec E P0 Pr P1 Uf γ.uFree =
      Polynomial.C γ.cg + Polynomial.C γ.ch * E + Polynomial.C γ.c0 * (P0 * E) +
        Polynomial.C γ.cr * Pr + Polynomial.C γ.c1 * P1 := by
  simp [ReprCoeffs.uFree, spec, η, x₀, xᵣ, x₁]

/-- The coefficient reading of Equations 20 and 21. If the forgery polynomial vanishes
in the ring, and the `u`-free parts of the commitment polynomials are those of the issued
representations `γ`, then the forgery's `U` representation `α` has no coefficient outside the tag
slots, no `V` coefficient, and every nonzero `U` coefficient `α.cu j` sits at a slot whose
representation has `x₁` coefficient `m`. -/
theorem forgeryPoly_eq_zero_coeffs (cs : Fin r → P F r) (γ : Fin r → ReprCoeffs F r)
    (hcs : ∀ k, ev0 (cs k) = (γ k).uFree) (m : F) (α β : ReprCoeffs F r)
    (h : omufForgeryPoly cs m α β = 0) :
    α.cg = 0 ∧ α.ch = 0 ∧ α.c0 = 0 ∧ α.cr = 0 ∧ α.c1 = 0 ∧ (∀ j, α.cv j = 0) ∧
      ∀ j, α.cu j * (m - (γ j).c1) = 0 := by
  -- The `u`-free part: specialize every `u` to `0`, and read one coefficient per tag slot.
  have hfree : ∀ E P0 Pr P1 : Polynomial F,
      (Polynomial.C α.cg + Polynomial.C α.ch * E + Polynomial.C α.c0 * (P0 * E) +
        Polynomial.C α.cr * Pr + Polynomial.C α.c1 * P1) * (P0 + Pr + Polynomial.C m * P1) =
      Polynomial.C β.cg + Polynomial.C β.ch * E + Polynomial.C β.c0 * (P0 * E) +
        Polynomial.C β.cr * Pr + Polynomial.C β.c1 * P1 := by
    intro E P0 Pr P1
    have h' := DFunLike.congr_arg (spec E P0 Pr P1 (fun _ => 0)) h
    rw [omufForgeryPoly, map_sub, map_mul, spec_toPolyAt_uZero, spec_toPolyAt_uZero,
      spec_keyPoly', map_zero] at h'
    linear_combination h'
  have hcg : α.cg = 0 := by
    have h2 := hfree 0 (Polynomial.X ^ 1) 0 0
    have h3 := congrArg (fun p => Polynomial.coeff p 1) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  have hcr : α.cr = 0 := by
    have h2 := hfree 0 0 (Polynomial.X ^ 1) 0
    have h3 := congrArg (fun p => Polynomial.coeff p 2) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  have hch : α.ch = 0 := by
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 2 + Polynomial.C α.ch * Polynomial.X ^ 3 +
          Polynomial.C α.cr * Polynomial.X ^ 4 =
        Polynomial.C β.cg + Polynomial.C β.ch * Polynomial.X ^ 1 +
          Polynomial.C β.cr * Polynomial.X ^ 2 := by
      linear_combination hfree (Polynomial.X ^ 1) 0 (Polynomial.X ^ 2) 0
    have h3 := congrArg (fun p => Polynomial.coeff p 3) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  have hc0 : α.c0 = 0 := by
    have h2 := hfree (Polynomial.X ^ 2) (Polynomial.X ^ 1) 0 0
    have h3 := congrArg (fun p => Polynomial.coeff p 4) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] using h3
  have hc1 : α.c1 = 0 := by
    have h2 : Polynomial.C α.cg * Polynomial.X ^ 2 +
          Polynomial.C α.cg * (Polynomial.C m * Polynomial.X ^ 1) +
          Polynomial.C α.c1 * Polynomial.X ^ 3 +
          Polynomial.C α.c1 * (Polynomial.C m * Polynomial.X ^ 2) =
        Polynomial.C β.cg + Polynomial.C β.c1 * Polynomial.X ^ 1 := by
      linear_combination hfree 0 (Polynomial.X ^ 2) 0 (Polynomial.X ^ 1)
    have h3 := congrArg (fun p => Polynomial.coeff p 3) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_C] using h3
  -- The `u_j`-linear part: differentiate in `u_j`, set the `u`s to `0`, and use `hcs`.
  have hlin : ∀ j (E P0 Pr P1 : Polynomial F),
      (Polynomial.C (α.cu j) + Polynomial.C (α.cv j) *
          (P0 + Pr + (Polynomial.C (γ j).cg + Polynomial.C (γ j).ch * E +
            Polynomial.C (γ j).c0 * (P0 * E) + Polynomial.C (γ j).cr * Pr +
            Polynomial.C (γ j).c1 * P1))) * (P0 + Pr + Polynomial.C m * P1) =
      Polynomial.C (β.cu j) + Polynomial.C (β.cv j) *
          (P0 + Pr + (Polynomial.C (γ j).cg + Polynomial.C (γ j).ch * E +
            Polynomial.C (γ j).c0 * (P0 * E) + Polynomial.C (γ j).cr * Pr +
            Polynomial.C (γ j).c1 * P1)) := by
    intro j E P0 Pr P1
    have h' := congrArg (fun p => spec E P0 Pr P1 (fun _ => 0)
      (ev0 (pderiv (Var.u j) p))) h
    simp only [map_zero] at h'
    rw [ev0_pderiv_u_forgeryPoly, ev0_pderiv_u_toPolyAt, ev0_pderiv_u_toPolyAt, hcs j] at h'
    simp only [map_sub, map_mul, map_add, spec_keyPoly', spec_uFree, spec_C, spec_x₀,
      spec_xᵣ] at h'
    linear_combination h'
  have hcv : ∀ j, α.cv j = 0 := by
    intro j
    have h2 := hlin j 0 (Polynomial.X ^ 1) 0 0
    have h3 := congrArg (fun p => Polynomial.coeff p 2) h2
    simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C, pow_two, Polynomial.coeff_mul_X,
      mul_add, add_mul] using h3
  refine ⟨hcg, hch, hc0, hcr, hc1, hcv, fun j => ?_⟩
  have hcu_eq : α.cu j = β.cv j := by
    have h2 := hlin j 0 (Polynomial.X ^ 1) 0 0
    have h3 := congrArg (fun p => Polynomial.coeff p 1) h2
    simpa [hcv j, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C, Polynomial.coeff_C_mul]
      using h3
  have hcu_m : α.cu j * m = β.cv j * (γ j).c1 := by
    have h2 := hlin j 0 0 0 (Polynomial.X ^ 1)
    have h3 := congrArg (fun p => Polynomial.coeff p 1) h2
    simpa [hcv j, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C, Polynomial.coeff_C_mul]
      using h3
  linear_combination hcu_m - (γ j).c1 * hcu_eq

end KVAC.Schemes.MicroCMZ.AGMPoly
