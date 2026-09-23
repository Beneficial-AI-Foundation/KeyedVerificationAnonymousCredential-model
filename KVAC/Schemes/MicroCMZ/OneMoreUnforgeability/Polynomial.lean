/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.AGMPolynomial

/-!
# μCMZ_AT one-more unforgeability — the polynomial layer of Equations 17 to 22 (O24 §5.6)

The pure-algebra layer of the Theorem 5.11 proof at `n = 1`, over Mathlib only
(no game imports), mirroring `AGMPolynomial.lean`, the Lemma 5.4 layer it
extends: the polynomials the proof reads off an algebraic transcript, in the
ring `AGMPoly.P F r = F[η, x₀, xᵣ, x₁, u₁, …, u_r]` of that file. Track CMZ-OMUF,
step A3 of the Theorem 5.3 plan, part 17a of item 17 (issue #189). This part
covers Equations 17 and 18, the commitment polynomials; Equation 22, the forgery
polynomial with the case split of the proof, follows in the next part.

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
    '---> omufCommitPolys γs        c_1, …, c_r by a left fold in issuance order,
                                    each fed the earlier ones                       (Eq 18)
          omufCommitPolys_nil, omufCommitPolys_append_singleton, omufCommitPolys_length

Next part: `omufForgeryPoly cs m* α β`, the forgery polynomial `φ` of Equation
22, `toPolyAt α · keyPoly m* − toPolyAt β`, and the three variable groups of the
proof's case split. `OneMoreUnforgeability/Transcript.lean` then reads all of
these off the game transcript (`OMUFTrace`) to define the case events that
Claims 5.12 to 5.14 bound (`Statements.lean`).

## What the proof phase owes this layer

The game-level evaluation bridge, the Equation 18 bridge announced in the
module docstring of `OneMoreUnforgeability/Game.lean`: at the discrete-log
point of an honest run, `c_k` evaluates to the logarithm of the `k`-th issued
commitment and `toPolyAt γ cs` to the
logarithm of the element `γ` represents, by induction over the transcript
through the gate and the server's honest answers, so that the forgery
polynomial of the next part vanishes at that point exactly when the
verification equation `V* = (x₀ + xᵣ + m*·x₁)·U*` holds (acceptance also needs
`U* ≠ 0`). `eval_toPolyAt` is its algebraic half;
the induction over the run is step A5 of the plan. So are the coefficient
identities of Equations 20 and 21 (in particular that, under the exact-length
gate, `u_k` occurs in `c_j` only for `k < j`), the degree bounds, and the
constant audit.

## Conventions

The fold of Equation 18 reads earlier polynomials through `List.getD … 0`, so a slot not yet
issued contributes `γ_{u,k}·u_k + γ_{v,k}·u_k·(x₀ + xᵣ)` rather than nothing;
for a representation accepted by the game's exact-length gate, the conversion
`toReprCoeffs` pads both coefficients of every not-yet-issued pair with `0`, so
the contribution is `0`. The layer itself accepts any coefficient lists, so
this triangularity is a property of gated inputs, stated in the proof phase.
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
γ_{v,k}·u_k·(x₀ + xᵣ + c_k)`. The OMUF twin of `ReprCoeffs.toPoly`, which has
`m_k·x₁` where this has `c_k` (module docstring, *Setting*).
-/
noncomputable def ReprCoeffs.toPolyAt (γ : ReprCoeffs F r) (cs : Fin r → P F r) : P F r :=
  C γ.cg + C γ.ch * η + C γ.c0 * (x₀ * η) + C γ.cr * xᵣ + C γ.c1 * x₁ +
    ∑ k, (C (γ.cu k) * u k + C (γ.cv k) * (u k * (x₀ + xᵣ + cs k)))

/-- Evaluation of `toPolyAt` at a point, in closed form: the algebraic half of
the Equation 18 bridge (module docstring, *What the proof phase owes this
layer*), the twin of `ReprCoeffs.eval_toPoly`. -/
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

/-- One more representation appends one more polynomial, fed the earlier ones:
the fold unrolled by one step, for reasoning about the `j`-th polynomial. -/
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

end KVAC.Schemes.MicroCMZ.AGMPoly
