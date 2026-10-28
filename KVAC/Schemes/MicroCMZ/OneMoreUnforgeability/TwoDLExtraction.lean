/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: cbannister
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Bridge
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.TwoDLReduction
import KVAC.Preliminaries.Assumptions

/-!
# μCMZ_AT one-more unforgeability — the extraction of Claim 5.14 (O24 §5.6, p. 47)

The second half of the proof of O24 Claim 5.14 for the three cases `x₀`, `xᵣ`, `x₁`, on top of
the reduction and its coupling of `TwoDLReduction.lean`: when the reduction's extraction can
succeed it does, and everything else is the event that does not depend on the reduction.
Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of item 17.

## What is proved

- `twoDLExtract_eq`: on a winning run whose forgery polynomials do not all vanish identically in
  the embedded variable once every other variable is set to the run's values, the reduction
  returns the challenge `x`. The substituted polynomial of a forgery vanishes at `x` by the
  evaluation bridge (`OMUFTrace.eval_point_of_wins`), and the root with `r·G = X` is `x`.
- `twoDL_claim_of_sound`: the probability of a case event is at most the degenerate-mask
  probability `1/p`, plus the 2-DL advantage of the reduction, plus the probability of the event
  together with the degeneracy of the run. The run of the reduction is the run of the game
  (`twoDLRunAt_trace`), the extraction succeeds off the degeneracy, and the challenge is
  recovered with the probability that defines the advantage.
- `omuf_claim_5_14_x0`, `omuf_claim_5_14_xr`, `omuf_claim_5_14_x1`: Claim 5.14 for each case, with
  the degenerate probability as an explicit extra term (`omufDegenerateProb`).

## The extraction obligation, and the bound proved instead

The paper's extraction substitutes the run's values for the other variables into the forgery
polynomial and treats the result as a polynomial in the challenge. A formal monomial in the embedded
variable does not make that polynomial nonzero: the forger chooses its forgery after Verify answers
that test the key, and it may guess hidden values (issue #251, errata
item 12). The statement that the degenerate case never happens, `Pr[Case ∧ Degenerate] = 0`, is
false as stated. A forger with no queries guesses `g` and forges
`(m, (H, X₀ + g·(Xᵣ + m·X₁)))`, with `m ≠ 0`. Since `X₀ = x₀·H` has logarithm `η·x₀`, its
polynomial is `(g − η)(xᵣ + m·x₁)`, nonzero formally, and it wins exactly when `g = η` (or
`xᵣ + m·x₁ = 0`), where the polynomial vanishes identically in `xᵣ` and in `x₁`. For `x₀`, a forger
that guesses `h` and forges `(m, (gen, h·X₀ + Xᵣ + m·X₁))` has the polynomial `(h·η − 1)·x₀`, which
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

section Probability

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- The reduction's experiment, unfolded: the challenge, then the run of the reduction at it. -/
noncomputable def twoDLExp (A : AGMOMUFAdversary F G 1) (w : F × F × F) :
    ProbComp (F × (TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G)) := do
  let x ← ($ᵗ F : ProbComp F)
  let r ← twoDLRunAt gen A w x
  pure (x, r)

/-- What the reduction outputs at a run of its experiment. -/
noncomputable def twoDLOutput (x : F)
    (r : TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G) : F :=
  twoDLExtract (twoDLTraceOf gen x r) gen (x • gen) r.1 (r.2.2.2.map Prod.fst)

/-- The 2-DL experiment of the reduction is its run at a uniform challenge, followed by the
comparison of its output with the challenge. -/
lemma qdlogExp_omufTwoDLReductionAt (A : AGMOMUFAdversary F G 1) (w : F × F × F) :
    qdlogExp 2 gen (omufTwoDLReductionAt gen A w) =
      (fun p => decide (twoDLOutput gen p.1 p.2 = p.1)) <$> twoDLExp gen A w := by
  have h0 : ∀ x : F, x ^ (((0 : Fin 2) : ℕ) + 1) • gen = x • gen := fun x => by simp
  have h1 : ∀ x : F, x ^ (((1 : Fin 2) : ℕ) + 1) • gen = x • (x • gen) := fun x => by
    simp [pow_two, smul_smul]
  simp only [qdlogExp, omufTwoDLReductionAt, twoDLExp, twoDLRunAt, twoDLOutput, map_bind,
    bind_pure_comp, h0, h1, Functor.map_map]
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G]
  hgen in
/-- Computations with the same evaluation distribution give every event the same probability. -/
lemma probEvent_eq_of_evalDist_eq' {α : Type} {mx my : ProbComp α} (h : 𝒟[mx] = 𝒟[my])
    (p : α → Prop) : Pr[p | mx] = Pr[p | my] := by
  rw [probEvent_def, probEvent_def, h]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G]
  hgen in
/-- A bad event of the sampler that every run outside it avoids has at most the probability of the
sampler's event. -/
lemma probEvent_bind_le_of_imp {α β : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (q : α → Prop) (p : β → Prop)
    (h : ∀ a ∈ support mx, ¬ q a → ∀ b ∈ support (my a), ¬ p b) :
    Pr[p | mx >>= my] ≤ Pr[q | mx] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : q a
  · rw [if_pos ha]
    exact (mul_le_mul' le_rfl probEvent_le_one).trans (mul_one _).le
  · rw [if_neg ha]
    by_cases hs : a ∈ support mx
    · have h0 : Pr[p | my a] = 0 := by
        rw [probEvent_eq_zero_iff]
        exact h a hs ha
      rw [h0, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul]

/-- The trace of the reduction's experiment is the trace of the game, in distribution. -/
lemma evalDist_twoDLExp_trace (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (w : F × F × F) :
    𝒟[(fun p => twoDLTraceOf gen p.1 p.2) <$> twoDLExp gen A w] =
      𝒟[agmOMUFTrace gen secParam A] := by
  have h : (fun p => twoDLTraceOf gen p.1 p.2) <$> twoDLExp gen A w =
      (do let x ← ($ᵗ F : ProbComp F); twoDLTraceOf gen x <$> twoDLRunAt gen A w x) := by
    simp [twoDLExp, monad_norm]
  rw [h]
  exact (evalDist_bind_congr' _ fun x => twoDLRunAt_trace gen secParam A w x).trans
    (evalDist_bind_uniform_const _)

/-- A run of the experiment gives a trace in the support of the game's. -/
lemma twoDLTraceOf_mem_support (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (w : F × F × F)
    (p : F × (TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G))
    (hp : p ∈ support (twoDLExp gen A w)) :
    twoDLTraceOf gen p.1 p.2 ∈ support (agmOMUFTrace gen secParam A) := by
  have hmem : twoDLTraceOf gen p.1 p.2 ∈
      support ((fun p => twoDLTraceOf gen p.1 p.2) <$> twoDLExp gen A w) := by
    rw [support_map]
    exact ⟨p, hp, rfl⟩
  rw [mem_support_iff, probOutput_def] at hmem ⊢
  rwa [← evalDist_twoDLExp_trace gen secParam A w]

omit hgen in
/-- A bad event of the slope that the embedding avoids away from `b = 0` has probability at most
`1/p`: the degenerate mask of the paper. -/
lemma probEvent_sampleEmbed_le (w : F × F × F) (Z : TwoDLEmbed F → Prop)
    (hZ : ∀ b : F, ∀ e ∈ support (twoDLEmbedAt w b), Z e → b = 0) :
    Pr[Z | twoDLSampleEmbed w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
  unfold twoDLSampleEmbed
  calc Pr[Z | (do let b ← ($ᵗ F : ProbComp F); twoDLEmbedAt w b)]
      ≤ Pr[(· = (0 : F)) | ($ᵗ F : ProbComp F)] :=
        probEvent_bind_le_of_imp _ _ _ _ fun b _ hb e he hZe => hb (hZ b e he hZe)
    _ = (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]

omit hgen in
/-- The degenerate-mask event of the reduction's experiment has at most the sampler's
probability. -/
lemma probEvent_twoDLExp_le (A : AGMOMUFAdversary F G 1) (w : F × F × F)
    (Z : TwoDLEmbed F → Prop) :
    Pr[fun p => Z p.2.1 | twoDLExp gen A w] ≤ Pr[Z | twoDLSampleEmbed w] := by
  unfold twoDLExp
  refine probEvent_bind_le_of_forall_le fun x _ => ?_
  unfold twoDLRunAt
  simp only [bind_assoc, pure_bind]
  refine probEvent_bind_le_of_imp _ _ Z _ fun e _ hne b hb => ?_
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hb
  obtain ⟨os, -, rfl⟩ := hb
  exact hne

/-- Events of the game's trace are events of the reduction's experiment read through
`twoDLTraceOf`. -/
lemma probEvent_agmOMUFTrace_eq (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (w : F × F × F)
    (Q : OMUFTrace F G → Prop) :
    Pr[Q | agmOMUFTrace gen secParam A] =
      Pr[fun p => Q (twoDLTraceOf gen p.1 p.2) | twoDLExp gen A w] := by
  rw [← probEvent_eq_of_evalDist_eq' (evalDist_twoDLExp_trace gen secParam A w) Q,
    probEvent_map]
  rfl

/-- The 2-DL advantage of the reduction is the probability that its output is the challenge. -/
lemma qdlogAdv_omufTwoDLReductionAt (A : AGMOMUFAdversary F G 1) (w : F × F × F) :
    qdlogAdv 2 gen (omufTwoDLReductionAt gen A w) =
      Pr[fun p => twoDLOutput gen p.1 p.2 = p.1 | twoDLExp gen A w] := by
  rw [qdlogAdv, qdlogExp_omufTwoDLReductionAt, ← probEvent_eq_eq_probOutput, probEvent_map]
  simp [Function.comp_def]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G]
  hgen in
/-- The arithmetic of the accounting. -/
lemma ennreal_accounting {c s z b D : ℝ≥0∞} (hcov : c ≤ s + (z + b)) (hz : z ≤ D) :
    c ≤ D + s + b := by
  calc c ≤ s + (z + b) := hcov
    _ ≤ s + (D + b) := add_le_add_right (add_le_add_left hz _) _
    _ = D + s + b := by ring

omit hgen in
/-- The union bound for an event covered by three on the support. -/
lemma probEvent_le_of_covered {β : Type} (J : ProbComp β) (E s z b : β → Prop)
    (h : ∀ p ∈ support J, E p → s p ∨ z p ∨ b p) :
    Pr[E | J] ≤ Pr[s | J] + (Pr[z | J] + Pr[b | J]) :=
  (probEvent_mono h).trans
    ((probEvent_or_le J s fun p => z p ∨ b p).trans
      (add_le_add_right (probEvent_or_le J z b) _))

/-- **The reduction's accounting.** The probability of a case event `P` is at most the
degenerate-mask probability `1/p`, plus the 2-DL advantage of the reduction, plus the probability
that `P` holds on a run that is degenerate: off the degeneracy, away from the mask, the
reduction's extraction returns the challenge (`hsound`). -/
theorem twoDL_claim_of_sound (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (w : F × F × F)
    (P Deg : OMUFTrace F G → Prop) (Z : TwoDLEmbed F → Prop)
    (hZ : Pr[Z | twoDLSampleEmbed w] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsound : ∀ p ∈ support (twoDLExp gen A w), P (twoDLTraceOf gen p.1 p.2) →
      ¬ Deg (twoDLTraceOf gen p.1 p.2) → ¬ Z p.2.1 → twoDLOutput gen p.1 p.2 = p.1) :
    Pr[P | agmOMUFTrace gen secParam A] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + qdlogAdv 2 gen (omufTwoDLReductionAt gen A w) +
        Pr[fun t => P t ∧ Deg t | agmOMUFTrace gen secParam A] := by
  rw [probEvent_agmOMUFTrace_eq gen secParam A w P,
    probEvent_agmOMUFTrace_eq gen secParam A w fun t => P t ∧ Deg t,
    qdlogAdv_omufTwoDLReductionAt gen A w]
  have hcov := probEvent_le_of_covered (twoDLExp gen A w)
    (fun p => P (twoDLTraceOf gen p.1 p.2))
    (fun p => twoDLOutput gen p.1 p.2 = p.1) (fun p => Z p.2.1)
    (fun p => P (twoDLTraceOf gen p.1 p.2) ∧ Deg (twoDLTraceOf gen p.1 p.2)) (by
      intro p hp hP
      by_cases hD : Deg (twoDLTraceOf gen p.1 p.2)
      · exact Or.inr (Or.inr ⟨hP, hD⟩)
      · by_cases hz : Z p.2.1
        · exact Or.inr (Or.inl hz)
        · exact Or.inl (hsound p hp hP hD hz))
  have hz := (probEvent_twoDLExp_le gen A w Z).trans hZ
  exact ennreal_accounting hcov hz

end Probability

section Claims

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))] (secParam : ℕ)

omit hgen in
/-- The slopes of an embedding drawn at the slope `b`. -/
lemma twoDLEmbedAt_support (w : F × F × F) (b : F) (e : TwoDLEmbed F)
    (he : e ∈ support (twoDLEmbedAt w b)) :
    e.b₀ = w.1 * b ∧ e.bᵣ = w.2.1 * b ∧ e.b₁ = w.2.2 * b := by
  simp only [twoDLEmbedAt, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at he
  obtain ⟨η, -, a₀, -, aᵣ, -, a₁, -, rfl⟩ := he
  exact ⟨rfl, rfl, rfl⟩

omit hgen in
/-- The slopes of an embedding the sampler draws. -/
lemma twoDLSampleEmbed_support (w : F × F × F) (e : TwoDLEmbed F)
    (he : e ∈ support (twoDLSampleEmbed w)) :
    ∃ b, e.b₀ = w.1 * b ∧ e.bᵣ = w.2.1 * b ∧ e.b₁ = w.2.2 * b := by
  simp only [twoDLSampleEmbed, mem_support_bind_iff] at he
  obtain ⟨b, -, hb⟩ := he
  exact ⟨b, twoDLEmbedAt_support w b e hb⟩

/-- What a run of the reduction's experiment guarantees: its trace is consistent, its records are
those of its log, and its embedding has the slopes the sampler draws. -/
lemma twoDLExp_facts (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (w : F × F × F)
    (p : F × (TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G))
    (hp : p ∈ support (twoDLExp gen A w)) :
    (twoDLTraceOf gen p.1 p.2).ServerConsistent gen ∧
      p.2.2.2.2 = twoDLAuxOf gen p.1 (AGMOMUFLog.tags p.2.2.2.1) ∧
      ∃ b, p.2.1.b₀ = w.1 * b ∧ p.2.1.bᵣ = w.2.1 * b ∧ p.2.1.b₁ = w.2.2 * b := by
  have hcons := OMUFTrace.serverConsistent_of_mem_support gen secParam A _
    (twoDLTraceOf_mem_support gen secParam A w p hp)
  have hrun : p.2 ∈ support (twoDLRunAt gen A w p.1) := by
    unfold twoDLExp at hp
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨x, -, r, hr, rfl⟩ := hp
    exact hr
  obtain ⟨he, hs⟩ := twoDLRunAt_support gen A w p.1 p.2 hrun
  exact ⟨hcons, hs, twoDLSampleEmbed_support w _ he⟩

/-- **O24 Claim 5.14, `x₀` case**, with the degenerate probability of the extraction as an extra
term (module docstring). -/
theorem omuf_claim_5_14_x0 (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseX0 gen secParam | agmOMUFTrace gen secParam A ] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + twoDlogAdv gen (omufTwoDLReductionAt gen A (1, 0, 0)) +
        Pr[ fun t => t.CaseX0 gen secParam ∧ t.Degenerate gen AGMPoly.Var.x0 |
          agmOMUFTrace gen secParam A ] := by
  have h := twoDL_claim_of_sound gen secParam A (1, 0, 0)
    (fun t => t.CaseX0 gen secParam) (fun t => t.Degenerate gen AGMPoly.Var.x0)
    (fun e => e.b₀ = 0)
    (probEvent_sampleEmbed_le _ _ fun b e he hz => by
      have := (twoDLEmbedAt_support _ b e he).1
      simpa [hz] using this.symm)
    (by
      rintro ⟨x, e, out, s⟩ hp hP hD hz
      obtain ⟨hcons, hs, b, h0, hr, h1⟩ := twoDLExp_facts gen secParam A _ _ hp
      exact twoDLExtract_eq gen secParam x e out s hs _ rfl hcons hP.1 AGMPoly.Var.x0
        (Or.inl ⟨rfl, by simpa using hr, by simpa using h1, hz⟩) hD)
  exact h

/-- **O24 Claim 5.14, `xᵣ` case** ("almost identical"), as `omuf_claim_5_14_x0`. -/
theorem omuf_claim_5_14_xr (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseXr gen secParam | agmOMUFTrace gen secParam A ] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + twoDlogAdv gen (omufTwoDLReductionAt gen A (0, 1, 0)) +
        Pr[ fun t => t.CaseXr gen secParam ∧ t.Degenerate gen AGMPoly.Var.xr |
          agmOMUFTrace gen secParam A ] := by
  have h := twoDL_claim_of_sound gen secParam A (0, 1, 0)
    (fun t => t.CaseXr gen secParam) (fun t => t.Degenerate gen AGMPoly.Var.xr)
    (fun e => e.bᵣ = 0)
    (probEvent_sampleEmbed_le _ _ fun b e he hz => by
      have := (twoDLEmbedAt_support _ b e he).2.1
      simpa [hz] using this.symm)
    (by
      rintro ⟨x, e, out, s⟩ hp hP hD hz
      obtain ⟨hcons, hs, b, h0, hr, h1⟩ := twoDLExp_facts gen secParam A _ _ hp
      exact twoDLExtract_eq gen secParam x e out s hs _ rfl hcons hP.1 AGMPoly.Var.xr
        (Or.inr (Or.inl ⟨rfl, by simpa using h0, by simpa using h1, hz⟩)) hD)
  exact h

/-- **O24 Claim 5.14, `x₁` case**, as `omuf_claim_5_14_x0`. -/
theorem omuf_claim_5_14_x1 (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseX1 gen secParam | agmOMUFTrace gen secParam A ] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + twoDlogAdv gen (omufTwoDLReductionAt gen A (0, 0, 1)) +
        Pr[ fun t => t.CaseX1 gen secParam ∧ t.Degenerate gen AGMPoly.Var.x1 |
          agmOMUFTrace gen secParam A ] := by
  have h := twoDL_claim_of_sound gen secParam A (0, 0, 1)
    (fun t => t.CaseX1 gen secParam) (fun t => t.Degenerate gen AGMPoly.Var.x1)
    (fun e => e.b₁ = 0)
    (probEvent_sampleEmbed_le _ _ fun b e he hz => by
      have := (twoDLEmbedAt_support _ b e he).2.2
      simpa [hz] using this.symm)
    (by
      rintro ⟨x, e, out, s⟩ hp hP hD hz
      obtain ⟨hcons, hs, b, h0, hr, h1⟩ := twoDLExp_facts gen secParam A _ _ hp
      exact twoDLExtract_eq gen secParam x e out s hs _ rfl hcons hP.1 AGMPoly.Var.x1
        (Or.inr (Or.inr ⟨rfl, by simpa using h0, by simpa using hr, hz⟩)) hD)
  exact h

end Claims

end KVAC.Schemes.MicroCMZ
