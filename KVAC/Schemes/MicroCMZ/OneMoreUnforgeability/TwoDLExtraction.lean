/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Callum Bannister
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Bridge
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.TwoDLReduction
import KVAC.Preliminaries.Assumptions

/-!
# μCMZ_AT one-more unforgeability — the extraction of Claim 5.14 (O24 §5.6, p. 47)

The second half of the proof of O24 Claim 5.14 for the three cases `x₀`, `xᵣ`, `x₁`, on top of
the reduction and its coupling of `TwoDLReduction.lean`: when the reduction's extraction can
succeed it does.
Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of item 17.

## What is proved

- `twoDLExtract_eq`: on a winning run whose forgery polynomials do not all vanish identically in
  the embedded variable once every other variable is set to the run's values, the reduction
  returns the challenge `x`. The substituted polynomial of a forgery vanishes at `x` by the
  evaluation bridge (`OMUFTrace.eval_point_of_wins`), and the root with `r·G = X` is `x`.

## The extraction obligation, and the bound proved instead

The paper's extraction substitutes the run's values for the other variables into the forgery
polynomial and treats the result as a polynomial in the challenge. A formal monomial in the embedded
variable does not make that polynomial nonzero: the forger chooses its forgery after Verify answers
that test the key, and it may guess hidden values (issue #251, errata
item 12). The statement that the degenerate case never happens, `Pr[Case ∧ Degenerate] = 0`, is
false as stated. A forger with no queries guesses `g` and forges
`(m, (H, X₀ + g·(Xᵣ + m·X₁)))`, with `m ≠ 0`. Since `X₀ = x₀·H` has logarithm `η·x₀`, its
polynomial `u·key − v` (Equation 22) is `(η − g)(xᵣ + m·x₁)`, nonzero formally, and it wins exactly
when `g = η` (or
`xᵣ + m·x₁ = 0`), where the polynomial vanishes identically in `xᵣ` and in `x₁`. For `x₀`, a forger
that guesses `h` and forges `(m, (gen, h·X₀ + Xᵣ + m·X₁))` has the polynomial `(1 − h·η)·x₀`, which
wins and vanishes identically in `x₀` when `h·η = 1`. So the degenerate event has probability
about `1/(p − 1)` for each variable.

The Claims here therefore carry the degenerate probability as an explicit term, which is a true
bound. It is not the paper's: removing the term is the repair of the paper's argument, by bounding
`omufDegenerateProb` or changing the events. They are statements about the real game alone, with no
reduction in them, so nothing else in this file changes.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

section Degenerate

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))] (secParam : ℕ)

/-- The forgery polynomial `φ` at the discrete-log point of the run, with the variable `v` kept:
the polynomial in `v` that the reduction embeds the challenge in, before the substitution
`v := a + b·χ`. -/
noncomputable def OMUFTrace.substPoly (t : OMUFTrace F G) (v : AGMPoly.Var t.arity) :
    AGMPoly.P F t.arity → Polynomial F :=
  MvPolynomial.aeval fun u => if u = v then Polynomial.X else Polynomial.C (t.point gen u)

/-- The run is *degenerate in `v`*: every forgery polynomial vanishes identically in `v` once the
other variables are evaluated at the run's values. Nothing can then be extracted by embedding the
challenge in `v`. -/
def OMUFTrace.Degenerate (t : OMUFTrace F G) (v : AGMPoly.Var t.arity) : Prop :=
  ∀ φ ∈ t.forgeryPolys, t.substPoly gen v φ = 0

/-- **The degenerate probability** of the Claim 5.14 extraction: the probability, summed over the
three cases, that the case event holds and the run is degenerate in the embedded variable, so that
the reduction has nothing to extract. The paper's argument treats it as `0`; it is not (module
docstring), and a repair bounds it or changes the events. -/
noncomputable def omufDegenerateProb (A : AGMOMUFAdversary F G 1) : ℝ≥0∞ :=
  Pr[ fun t => t.CaseX0 gen secParam ∧ t.Degenerate gen AGMPoly.Var.x0 |
      agmOMUFTrace gen secParam A ] +
    (Pr[ fun t => t.CaseXr gen secParam ∧ t.Degenerate gen AGMPoly.Var.xr |
        agmOMUFTrace gen secParam A ] +
      Pr[ fun t => t.CaseX1 gen secParam ∧ t.Degenerate gen AGMPoly.Var.x1 |
        agmOMUFTrace gen secParam A ])

end Degenerate

section Support

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- A run in the support of the reduction draws its randomness from the sampler, and its records
are those of its log. -/
lemma twoDLRunAt_support (A : AGMOMUFAdversary F G 1) (w : F × F × F) (x : F)
    (r : TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G)
    (hr : r ∈ support (twoDLRunAt gen A w x)) :
    r.1 ∈ support (twoDLSampleEmbed w) ∧
      r.2.2.2 = twoDLAuxOf gen x (AGMOMUFLog.tags r.2.2.1) := by
  obtain ⟨e, out, s⟩ := r
  unfold twoDLRunAt at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨e', he', hr'⟩ := hr
  rw [mem_support_bind_iff] at hr'
  obtain ⟨⟨out', s'⟩, hos, hpure⟩ := hr'
  rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hpure
  obtain ⟨rfl, rfl, rfl⟩ := hpure
  refine ⟨he', ?_⟩
  have h := twoDL_run gen 0 x e (A.run (e.η • gen) (twoDLParams gen (x • gen) e)) []
  have h0 : twoDLAuxOf gen x (AGMOMUFLog.tags ([] : AGMOMUFLog F G 1)) = [] := rfl
  rw [h0] at h
  rw [h, support_map] at hos
  obtain ⟨p, -, hp⟩ := hos
  rw [Prod.mk.injEq] at hp
  rw [← hp.2]

end Support

section Soundness

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
/-- Evaluating a substituted polynomial at `x` is evaluating the polynomial at the values of the
substitution at `x`. -/
lemma eval_aeval_polynomial {σ : Type} (pt : σ → Polynomial F) (φ : MvPolynomial σ F) (x : F) :
    Polynomial.eval x (MvPolynomial.aeval pt φ) =
      MvPolynomial.eval (fun u => Polynomial.eval x (pt u)) φ := by
  have h := congrArg (fun f => f φ) (MvPolynomial.comp_aeval (R := F) (f := pt)
    (Polynomial.aeval x))
  simpa [Polynomial.coe_aeval_eq_eval, MvPolynomial.coe_aeval_eq_eval] using h

/-- The substitution of the extraction, evaluated at the challenge, is the discrete-log point of
the run: the values the reduction sampled or recorded are the logarithms the bridge speaks of. -/
lemma twoDLSubst_eval (x : F) (e : TwoDLEmbed F) (out : List (AGMOMUFForgery F G 1))
    (s : TwoDLState F G) (hs : s.2 = twoDLAuxOf gen x (AGMOMUFLog.tags s.1))
    (u : AGMPoly.Var (twoDLTraceOf gen x (e, out, s)).arity) :
    Polynomial.eval x (twoDLSubst e (s.2.map Prod.fst) _ u) =
      (twoDLTraceOf gen x (e, out, s)).point gen u := by
  cases u with
  | eta => simp [twoDLSubst, OMUFTrace.point, gamePoint, twoDLTraceOf, glog_smul_self]
  | x0 => simp [twoDLSubst, OMUFTrace.point, gamePoint, twoDLTraceOf, TwoDLEmbed.key]
  | xr => simp [twoDLSubst, OMUFTrace.point, gamePoint, twoDLTraceOf, TwoDLEmbed.key]
  | x1 => simp [twoDLSubst, OMUFTrace.point, gamePoint, twoDLTraceOf, TwoDLEmbed.key]
  | u j =>
    simp only [twoDLSubst, Polynomial.eval_C, OMUFTrace.point, gamePoint, twoDLTraceOf]
    rw [hs]
    simp [twoDLAuxOf, List.getD_eq_getElem?_getD]

/-- The extraction returns the challenge when the run wins and is not degenerate in the embedded
variable `v`, whose substituted value is the non-constant polynomial `lin` and every other
variable's a constant. -/
lemma twoDLExtract_eq_aux (secParam : ℕ) (x : F) (e : TwoDLEmbed F)
    (out : List (AGMOMUFForgery F G 1)) (s : TwoDLState F G)
    (hs : s.2 = twoDLAuxOf gen x (AGMOMUFLog.tags s.1))
    (t : OMUFTrace F G) (ht : t = twoDLTraceOf gen x (e, out, s))
    (hcons : t.ServerConsistent gen) (hw : t.Wins gen secParam)
    (v : AGMPoly.Var t.arity) (lin : Polynomial F)
    (hvlin : twoDLSubst e (s.2.map Prod.fst) t.arity v = lin) (hnc : ∀ c, lin ≠ Polynomial.C c)
    (hconst : ∀ u, u ≠ v → ∃ c, twoDLSubst e (s.2.map Prod.fst) t.arity u = Polynomial.C c)
    (hnd : ¬ t.Degenerate gen v) :
    twoDLExtract t gen (x • gen) e (s.2.map Prod.fst) = x := by
  have hpt : ∀ u : AGMPoly.Var t.arity,
      Polynomial.eval x (twoDLSubst e (s.2.map Prod.fst) t.arity u) = t.point gen u := by
    subst ht
    exact twoDLSubst_eval gen x e out s hs
  -- the substitution is the substituted polynomial composed with `lin`
  have hfun : twoDLSubst e (s.2.map Prod.fst) t.arity = fun u =>
      (Polynomial.aeval lin) (if u = v then Polynomial.X else Polynomial.C (t.point gen u)) := by
    funext u
    by_cases hu : u = v
    · subst hu
      simp [hvlin]
    · obtain ⟨c, hc⟩ := hconst u hu
      have hpu : t.point gen u = c := by rw [← hpt u, hc, Polynomial.eval_C]
      simp [hu, hpu, hc]
  have hcomp : ∀ φ : AGMPoly.P F t.arity,
      MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity) φ =
        (t.substPoly gen v φ).comp lin := by
    intro φ
    have h := congrArg (fun f => f φ) (MvPolynomial.comp_aeval (R := F)
      (f := fun u => if u = v then Polynomial.X else Polynomial.C (t.point gen u))
      (Polynomial.aeval lin))
    simp only [AlgHom.comp_apply] at h
    rw [OMUFTrace.substPoly, Polynomial.comp_eq_aeval, h, hfun]
  -- the polynomial of some forgery is nonzero
  obtain ⟨φ₀, hφ₀, hne⟩ : ∃ φ ∈ t.forgeryPolys, t.substPoly gen v φ ≠ 0 := by
    simpa [OMUFTrace.Degenerate] using hnd
  have hp0 : MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity) φ₀ ≠ 0 := by
    rw [hcomp]
    intro h
    rw [Polynomial.comp_eq_zero_iff] at h
    rcases h with h | ⟨-, h⟩
    · exact hne h
    · exact hnc _ h
  -- every substituted forgery polynomial vanishes at the challenge
  have hroot : ∀ φ ∈ t.forgeryPolys,
      Polynomial.eval x (MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity) φ) = 0 := by
    intro φ hφ
    rw [eval_aeval_polynomial, show (fun u => Polynomial.eval x
        (twoDLSubst e (s.2.map Prod.fst) t.arity u)) = t.point gen from funext hpt]
    exact t.eval_point_of_wins gen secParam hcons hw φ hφ
  unfold twoDLExtract
  have hsome : ((t.forgeryPolys.map fun φ =>
      MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity) φ).find?
        (fun p => decide (p ≠ 0))).isSome := by
    rw [List.find?_isSome]
    exact ⟨_, List.mem_map_of_mem hφ₀, by simpa using hp0⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsome
  rw [hp]
  dsimp only
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hp)
  have hpne : MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity) φ ≠ 0 := by
    simpa using List.find?_some hp
  have hxr : x ∈ (MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity) φ).roots.toList :=
    Multiset.mem_toList.2 ((Polynomial.mem_roots hpne).2 (hroot φ hφ))
  have hsome' : ((MvPolynomial.aeval (twoDLSubst e (s.2.map Prod.fst) t.arity)
      φ).roots.toList.find? (fun r : F => decide (r • gen = x • gen))).isSome := by
    rw [List.find?_isSome]
    exact ⟨x, hxr, by simp⟩
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hsome'
  rw [hr']
  exact hgen.out.1 (by simpa using List.find?_some hr')

/-- **Extraction soundness.** On a winning run of the reduction that is not degenerate in the
embedded variable, the reduction returns the challenge. The embedded variable carries the nonzero
slope, the other two key variables slope `0`. -/
theorem twoDLExtract_eq (secParam : ℕ) (x : F) (e : TwoDLEmbed F)
    (out : List (AGMOMUFForgery F G 1)) (s : TwoDLState F G)
    (hs : s.2 = twoDLAuxOf gen x (AGMOMUFLog.tags s.1))
    (t : OMUFTrace F G) (ht : t = twoDLTraceOf gen x (e, out, s))
    (hcons : t.ServerConsistent gen) (hw : t.Wins gen secParam) (v : AGMPoly.Var t.arity)
    (hv : (v = AGMPoly.Var.x0 ∧ e.bᵣ = 0 ∧ e.b₁ = 0 ∧ e.b₀ ≠ 0) ∨
      (v = AGMPoly.Var.xr ∧ e.b₀ = 0 ∧ e.b₁ = 0 ∧ e.bᵣ ≠ 0) ∨
      (v = AGMPoly.Var.x1 ∧ e.b₀ = 0 ∧ e.bᵣ = 0 ∧ e.b₁ ≠ 0))
    (hnd : ¬ t.Degenerate gen v) :
    twoDLExtract t gen (x • gen) e (s.2.map Prod.fst) = x := by
  rcases hv with ⟨rfl, hbr, hb1, hb0⟩ | ⟨rfl, hb0, hb1, hbr⟩ | ⟨rfl, hb0, hbr, hb1⟩
  · refine twoDLExtract_eq_aux gen secParam x e out s hs t ht hcons hw _
      (Polynomial.C e.a₀ + Polynomial.C e.b₀ * Polynomial.X) rfl ?_ ?_ hnd
    · intro c h
      have := congrArg (fun p => Polynomial.coeff p 1) h
      simp at this
      exact hb0 this
    · intro u hu
      rcases u with _ | _ | _ | _ | j
      · exact ⟨e.η, rfl⟩
      · exact absurd rfl hu
      · exact ⟨e.aᵣ, by simp [twoDLSubst, hbr]⟩
      · exact ⟨e.a₁, by simp [twoDLSubst, hb1]⟩
      · exact ⟨_, rfl⟩
  · refine twoDLExtract_eq_aux gen secParam x e out s hs t ht hcons hw _
      (Polynomial.C e.aᵣ + Polynomial.C e.bᵣ * Polynomial.X) rfl ?_ ?_ hnd
    · intro c h
      have := congrArg (fun p => Polynomial.coeff p 1) h
      simp at this
      exact hbr this
    · intro u hu
      rcases u with _ | _ | _ | _ | j
      · exact ⟨e.η, rfl⟩
      · exact ⟨e.a₀, by simp [twoDLSubst, hb0]⟩
      · exact absurd rfl hu
      · exact ⟨e.a₁, by simp [twoDLSubst, hb1]⟩
      · exact ⟨_, rfl⟩
  · refine twoDLExtract_eq_aux gen secParam x e out s hs t ht hcons hw _
      (Polynomial.C e.a₁ + Polynomial.C e.b₁ * Polynomial.X) rfl ?_ ?_ hnd
    · intro c h
      have := congrArg (fun p => Polynomial.coeff p 1) h
      simp at this
      exact hb1 this
    · intro u hu
      rcases u with _ | _ | _ | _ | j
      · exact ⟨e.η, rfl⟩
      · exact ⟨e.a₀, by simp [twoDLSubst, hb0]⟩
      · exact ⟨e.aᵣ, by simp [twoDLSubst, hbr]⟩
      · exact absurd rfl hu
      · exact ⟨_, rfl⟩

end Soundness

end KVAC.Schemes.MicroCMZ
