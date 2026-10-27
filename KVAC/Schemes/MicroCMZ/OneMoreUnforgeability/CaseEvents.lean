/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Transcript
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Polynomial
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

/-!
# μCMZ_AT one-more unforgeability — the polynomials and case events of a run (O24 §5.6)

The polynomials of Equations 18 and 22 (`Polynomial.lean`) read off the game
transcript (`Transcript.lean`), and the win and the three case events of the
Theorem 5.11 proof's case split at `n = 1`, items (i) to (iii) of p. 45, that
Claims 5.12 to 5.14 bound in `Statements.lean`. Track CMZ-OMUF, step A3 of the
Theorem 5.3 plan, part 17a of item 17 (issue #189).

## What is defined, and what uses it

  t : OMUFTrace F G   (sk, H, pp, log, out)   the record of a run, Transcript.lean
    |---> t.issuedReprs        representations of the issued commitments, in order
    |                          issuedReprs_length: one per issued pair            (proved)
    |---> t.arity              the number r of issued pairs, (tags log).length
    |---> t.commitPolys, t.cs  c_1 … c_r     omufCommitPolys of toReprCoeffs      (Eq 18)
    |                          commitPolys_length, cs_eq_getElem                  (proved)
    |---> t.forgeryPolys       one φ per forgery, omufForgeryPoly at t.cs         (Eq 22)
    '---> t.Wins, t.CaseU, t.CaseEta, t.CaseX
                               the win and the three case events, items (i) to (iii),
                               the events Claims 5.12 to 5.14 bound

`AGMRepr.toReprCoeffs` of `AGMReduction/Core.lean` converts a game
representation to polynomial-layer coefficients at a given arity, reading
absent tag slots as `0`, which under the exact-length gate is the right value.
The arity is the number of issued pairs, not the Sign budget, since a refused
Sign query issues no pair and gets no variable, while the winning condition
counts every Sign query.

## The evaluation bridge

The game-level evaluation bridge: at the discrete-log point of a run (`OMUFTrace.point` in
`Statements.lean`), `t.cs k` evaluates to the logarithm of the `k`-th issued commitment and,
for a forgery whose representations match its token and whose token verifies, its polynomial
vanishes (`eval_point_cs`, `eval_point_forgeryPoly`), by induction over the transcript through
the gate and the server's answers. Its algebraic half is `eval_toPolyAt` in `Polynomial.lean`;
the induction needs the invariants of a run, recovered from membership in the support of
`agmOMUFTrace` (`serverConsistent_of_mem_support`).
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

section Events

variable (gen : G) (secParam : ℕ)

/-- The representations of the issued commitments, in issuance order, aligned
with the issued pairs `AGMOMUFLog.tags`: the `γ⃗^(j)` of O24 Equation 17. -/
def OMUFTrace.issuedReprs (t : OMUFTrace F G) : List (AGMRepr F 1) :=
  t.log.filterMap fun e => e.2.2.map fun _ => e.2.1

/-- The number of issued pairs, the arity `r` of the polynomial ring of the run. -/
abbrev OMUFTrace.arity (t : OMUFTrace F G) : ℕ := (AGMOMUFLog.tags t.log).length

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G]
  [SampleableGroup F G] in
/-- One issued representation per issued pair. -/
theorem OMUFTrace.issuedReprs_length (t : OMUFTrace F G) :
    t.issuedReprs.length = t.arity := by
  unfold OMUFTrace.issuedReprs OMUFTrace.arity AGMOMUFLog.tags
  induction t.log with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨_, _, resp?⟩
    cases resp?
    · simp only [Option.map_none, List.filterMap_cons_none, ih]
    · simp only [Option.map_some, Option.some.injEq, List.filterMap_cons_some,
        List.length_cons, ih]

/-- The commitment polynomials `c_1, …, c_r` of the run (O24 Equation 18). -/
noncomputable def OMUFTrace.commitPolys (t : OMUFTrace F G) : List (AGMPoly.P F t.arity) :=
  AGMPoly.omufCommitPolys (t.issuedReprs.map fun ρ => ρ.toReprCoeffs t.arity)

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] in
/-- One commitment polynomial per issued pair. -/
theorem OMUFTrace.commitPolys_length (t : OMUFTrace F G) : t.commitPolys.length = t.arity := by
  unfold OMUFTrace.commitPolys
  rw [AGMPoly.omufCommitPolys_length, List.length_map, OMUFTrace.issuedReprs_length]

/-- The commitment polynomials indexed by issuance position, `0` past the list,
which `cs_eq_getElem` shows is never reached. -/
noncomputable def OMUFTrace.cs (t : OMUFTrace F G) : Fin t.arity → AGMPoly.P F t.arity :=
  fun j => t.commitPolys.getD j 0

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] in
/-- `cs` is the list itself at every position of the arity. -/
theorem OMUFTrace.cs_eq_getElem (t : OMUFTrace F G) (j : Fin t.arity) :
    t.cs j = t.commitPolys[j.val]'(by rw [OMUFTrace.commitPolys_length]; exact j.isLt) := by
  unfold OMUFTrace.cs
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

/-- The `j`-th issued representation, the `γ⃗^(j)` of O24 Equation 17. -/
def OMUFTrace.issuedRepr (t : OMUFTrace F G) (j : Fin t.arity) : AGMRepr F 1 :=
  t.issuedReprs[j.1]'(by rw [t.issuedReprs_length]; exact j.2)

/-- The coefficients of the `j`-th issued representation, the `γ^(j)` of O24 Equation 17 over
the ring of the run. -/
noncomputable def OMUFTrace.issuedCoeffs (t : OMUFTrace F G) (j : Fin t.arity) :
    AGMPoly.ReprCoeffs F t.arity :=
  (t.issuedRepr j).toReprCoeffs t.arity

/-- The forgery polynomials `φ_i` of the run (O24 Equation 22), one per forgery,
at the run's commitment polynomials. -/
noncomputable def OMUFTrace.forgeryPolys (t : OMUFTrace F G) : List (AGMPoly.P F t.arity) :=
  t.out.map fun e =>
    AGMPoly.omufForgeryPoly t.cs (e.msg 0) (e.reprU.toReprCoeffs t.arity)
      (e.reprV.toReprCoeffs t.arity)

/-- The winning condition read off a trace. -/
def OMUFTrace.Wins (t : OMUFTrace F G) : Prop :=
  AGMOMUFWins gen secParam t.sk t.H t.pp t.log t.out

/-- Item (i) of the case split (p. 45): the adversary wins and some forgery
polynomial has a nonzero monomial in some `u_j`. The event Claim 5.12 bounds. -/
def OMUFTrace.CaseU (t : OMUFTrace F G) : Prop :=
  t.Wins gen secParam ∧ ∃ φ ∈ t.forgeryPolys, AGMPoly.HasUMonomial φ

/-- Item (ii): the adversary wins and some forgery polynomial has a nonzero
monomial in `η`. The event Claim 5.13 bounds. -/
def OMUFTrace.CaseEta (t : OMUFTrace F G) : Prop :=
  t.Wins gen secParam ∧ ∃ φ ∈ t.forgeryPolys, AGMPoly.HasEtaMonomial φ

/-- Item (iii): the adversary wins and some forgery polynomial has a nonzero
monomial in `x₀`, `xᵣ` or `x₁`. The event Claim 5.14 bounds. -/
def OMUFTrace.CaseX (t : OMUFTrace F G) : Prop :=
  t.Wins gen secParam ∧ ∃ φ ∈ t.forgeryPolys, AGMPoly.HasXMonomial φ

/-- Item (iii), `x₀` case (p. 47): the adversary wins and some forgery polynomial has a nonzero
monomial in `x₀`. The event the `x₀` reduction of Claim 5.14 bounds. -/
def OMUFTrace.CaseX0 (t : OMUFTrace F G) : Prop :=
  t.Wins gen secParam ∧ ∃ φ ∈ t.forgeryPolys, AGMPoly.Var.x0 ∈ φ.vars

/-- Item (iii), `xᵣ` case: as `CaseX0` for `xᵣ`. -/
def OMUFTrace.CaseXr (t : OMUFTrace F G) : Prop :=
  t.Wins gen secParam ∧ ∃ φ ∈ t.forgeryPolys, AGMPoly.Var.xr ∈ φ.vars

/-- Item (iii), `x₁` case: as `CaseX0` for `x₁`. -/
def OMUFTrace.CaseX1 (t : OMUFTrace F G) : Prop :=
  t.Wins gen secParam ∧ ∃ φ ∈ t.forgeryPolys, AGMPoly.Var.x1 ∈ φ.vars

/-- Item (iii) is the union of its three cases. -/
theorem OMUFTrace.caseX_imp (t : OMUFTrace F G) (h : t.CaseX gen secParam) :
    t.CaseX0 gen secParam ∨ t.CaseXr gen secParam ∨ t.CaseX1 gen secParam := by
  obtain ⟨hw, φ, hφ, h0 | hr | h1⟩ := h
  · exact Or.inl ⟨hw, φ, hφ, h0⟩
  · exact Or.inr (Or.inl ⟨hw, φ, hφ, hr⟩)
  · exact Or.inr (Or.inr ⟨hw, φ, hφ, h1⟩)

end Events

end KVAC.Schemes.MicroCMZ
