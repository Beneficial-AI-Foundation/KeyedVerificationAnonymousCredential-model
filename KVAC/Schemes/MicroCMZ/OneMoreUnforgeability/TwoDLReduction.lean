/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Callum Bannister
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.CaseEvents
import KVAC.Preliminaries.Assumptions

/-!
# μCMZ_AT one-more unforgeability — the 2-DL reductions of Claim 5.14 (O24 §5.6, p. 47)

The reduction `B(Γ, X, X')` of the proof of O24 Claim 5.14, built from an algebraic one-more
forger `A` (`omufTwoDLReductionAt`), and the coupling of its simulation with the real game
(`twoDL_run`). Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of item 17.

## The reduction

The paper embeds the challenge in `x₀` and calls the cases `xᵣ` and `x₁` "almost identical". All
three are one construction with a key that is affine in the challenge `x` in every component,
`(x₀, xᵣ, x₁) = (a₀ + b₀·x, aᵣ + bᵣ·x, a₁ + b₁·x)` (`TwoDLEmbed`), the case being the choice of
which slopes are nonzero: `b₀ = b` and the others `0` for `x₀`, and so on.

`B` samples `η` and the offsets and slopes and runs `A` on `H := η·G`, `X₀ := a₀·H + b₀·η·X`,
`Xᵣ := aᵣ·G + bᵣ·X`, `X₁ := a₁·G + b₁·X`, the public parameters of that key. Sign is answered as
the paper prescribes, `U := u·G`, `V := a₀·U + b₀·u·X + u·(C + Xᵣ)`, which needs no knowledge of
`x`. Verify tests `V = (x₀ + xᵣ + m·x₁)·U`, with the key above, as
`V = (a₀ + aᵣ + m·a₁)·U + (b₀ + bᵣ + m·b₁)·(x·U)`, so the reduction needs the group element
`x·U`. The representation of `U` is a combination of the basis `G, H, X₀, Xᵣ, X₁` and of the
issued pairs, each of which has a known multiple by `x`: `x·G = X`, `x·H = η·X`, and
`x·X₀ = a₀·η·X + b₀·η·X'` and the like for `Xᵣ` and `X₁` (this is where `X' = x²·G` enters, "the
quadratic term"), and, for the issued pairs, the multiples `x·U_j = u_j·X` and `x·V_j`, which the
reduction records as it answers Sign, the latter from the multiple `x·C_j` of the commitment,
itself a combination of the same kind. The reduction's state is the game's log with these
records: `(u_j, x·V_j)` per issued pair.

## The coupling

With the key above the simulated oracles and the real ones agree query by query, the records
being a function of the log (`twoDLAuxOf`), so the simulated run is the real run followed by that
function (`twoDL_run`), an equality of computations, not of distributions. What remains for the
Claim is the distribution of the key and of `H` (the slope times `x` is uniform given the slope,
which is the perfect hiding by the offset of the paper) and the extraction.

## The extraction

At the end `B` reads the forgery polynomials of the run (`OMUFTrace.forgeryPolys`), substitutes
the key variables by the affine functions of `χ` and the values it sampled or recorded for every
other variable, and outputs the root `r` of the first nonzero univariate polynomial with
`r·G = X` (`twoDLExtract`). Whether that polynomial is nonzero is the extraction obligation of
`Statements.lean`. The root is chosen classically, from `Polynomial.roots`, so `twoDLExtract` is
noncomputable: the statements about it say which root it returns, not that it is computed
efficiently. The repository's advantage statements do not model running time, as elsewhere in the
development, and finding the roots of a polynomial of bounded degree over `F` is efficient but
is not formalized.

## The mixture

The three cases are mixed into the single 2-DL adversary of the theorem, with a uniform choice
of case independent of the challenge (`twoDLMix`), so that `3·Adv(mixture)` is the sum of the
three advantages (`qdlogAdv_twoDLMix`), the factor `3` of Claim 5.14.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

/-- The randomness of the reduction: the crs logarithm `η` and the key
`(a₀ + b₀·x, aᵣ + bᵣ·x, a₁ + b₁·x)`, affine in the challenge `x`. -/
structure TwoDLEmbed (F : Type) where
  /-- `η = log H`. -/
  η : F
  /-- Offset of `x₀`. -/
  a₀ : F
  /-- Slope of `x₀`. -/
  b₀ : F
  /-- Offset of `xᵣ`. -/
  aᵣ : F
  /-- Slope of `xᵣ`. -/
  bᵣ : F
  /-- Offset of `x₁`. -/
  a₁ : F
  /-- Slope of `x₁`. -/
  b₁ : F

/-- The key at the challenge `x`. -/
def TwoDLEmbed.key (e : TwoDLEmbed F) (x : F) : Key F 1 :=
  (e.a₀ + e.b₀ * x, e.aᵣ + e.bᵣ * x, fun _ => e.a₁ + e.b₁ * x)

section Oracle

variable (g X X' : G) (e : TwoDLEmbed F)

/-- The public parameters the reduction hands `A`: those of the key `e.key x`, for `H = η·G`. -/
def twoDLParams : Params G 1 :=
  (e.a₀ • (e.η • g) + (e.b₀ * e.η) • X, e.aᵣ • g + e.bᵣ • X, fun _ => e.a₁ • g + e.b₁ • X)

/-- The reduction's state: the game's log, with `(u_j, x·V_j)` for each issued pair. -/
abbrev TwoDLState (F G : Type) : Type := AGMOMUFLog F G 1 × List (F × G)

/-- The multiples by `x` of the issued pairs, from the records: `x·U_j = u_j·X`. -/
def twoDLXTags (aux : List (F × G)) : List (G × G) :=
  aux.map fun p => (p.1 • X, p.2)

/-- The multiple by `x` of the group element that a representation names: the same combination
of the multiples by `x` of the basis, `x·G = X`, `x·H = η·X`, `x·X₀ = a₀·η·X + b₀·η·X'`,
`x·Xᵣ = aᵣ·X + bᵣ·X'`, `x·X₁ = a₁·X + b₁·X'`, and of the issued pairs. -/
def twoDLxEval (ρ : AGMRepr F 1) (aux : List (F × G)) : G :=
  ρ.eval X (e.η • X) ((e.a₀ * e.η) • X + (e.b₀ * e.η) • X') (e.aᵣ • X + e.bᵣ • X')
    (fun _ => e.a₁ • X + e.b₁ • X') (twoDLXTags X aux)

/-- The reduction's answers to the two oracle arms, without the key. -/
noncomputable def twoDLOracleImpl :
    QueryImpl (AGMOMUFOracleSpec F G 1) (StateT (TwoDLState F G) ProbComp)
  | .sign C' ρ => StateT.mk fun s =>
      if reprMatches ρ g (e.η • g) (twoDLParams g X e).1 (twoDLParams g X e).2.1
          (twoDLParams g X e).2.2 (AGMOMUFLog.tags s.1) C' then do
        let u ← uniformUnits F
        let U := u • g
        let V := e.a₀ • U + (e.b₀ * u) • X + u • (C' + (e.aᵣ • g + e.bᵣ • X))
        let xV := e.a₀ • (u • X) + (e.b₀ * u) • X' +
          u • (twoDLxEval X X' e ρ s.2 + (e.aᵣ • X + e.bᵣ • X'))
        pure (some (U, V), (s.1 ++ [(C', ρ, some (U, V))], s.2 ++ [(u, xV)]))
      else pure (none, (s.1 ++ [(C', ρ, none)], s.2))
  | .verify m σ ρU ρV => StateT.mk fun s =>
      let pp := twoDLParams g X e
      let tags := AGMOMUFLog.tags s.1
      let consistent :=
        reprMatches ρU g (e.η • g) pp.1 pp.2.1 pp.2.2 tags σ.1 ∧
        reprMatches ρV g (e.η • g) pp.1 pp.2.1 pp.2.2 tags σ.2
      pure (decide consistent && (decide (σ.1 ≠ 0) &&
        decide (σ.2 = (e.a₀ + e.aᵣ + e.a₁ * m 0) • σ.1 +
          (e.b₀ + e.bᵣ + e.b₁ * m 0) • twoDLxEval X X' e ρU s.2)), s)

/-- The full implementation: coin queries lifted, the instrumented queries through
`twoDLOracleImpl`. -/
noncomputable def twoDLImpl :
    QueryImpl (unifSpec + AGMOMUFOracleSpec F G 1) (StateT (TwoDLState F G) ProbComp) :=
  HAdd.hAdd
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (TwoDLState F G) ProbComp))
    (twoDLOracleImpl g X X' e)

end Oracle

section Extraction

open Classical in
/-- The extraction of the reduction: substitute the key variables by their affine functions of
`χ` and the sampled or recorded values `η, u_j` into the forgery polynomials of the run, and
output the root with `r·G = X` of the first one that is nonzero, `0` if there is none. -/
noncomputable def twoDLExtract (t : OMUFTrace F G) (g X : G) (e : TwoDLEmbed F)
    (us : List F) : F :=
  let pt : AGMPoly.Var t.arity → Polynomial F
    | .eta => Polynomial.C e.η
    | .x0 => Polynomial.C e.a₀ + Polynomial.C e.b₀ * Polynomial.X
    | .xr => Polynomial.C e.aᵣ + Polynomial.C e.bᵣ * Polynomial.X
    | .x1 => Polynomial.C e.a₁ + Polynomial.C e.b₁ * Polynomial.X
    | .u j => Polynomial.C (us.getD j 0)
  match (t.forgeryPolys.map fun φ => MvPolynomial.aeval pt φ).find? (fun p => decide (p ≠ 0)) with
  | some p => (p.roots.toList.find? fun r => decide (r • g = X)).getD 0
  | none => 0

end Extraction

section Reduction

/-- The reduction's randomness for the slope pattern `w` at the slope `b`: the crs logarithm `η`,
nonzero as `setup` draws `H` from the nonzero elements, and the offsets. The key variable with
weight `1` gets the slope `b`, the others slope `0`. -/
noncomputable def twoDLEmbedAt (w : F × F × F) (b : F) : ProbComp (TwoDLEmbed F) := do
  let η ← uniformUnits F
  let a₀ ← $ᵗ F
  let aᵣ ← $ᵗ F
  let a₁ ← $ᵗ F
  pure ⟨η, a₀, w.1 * b, aᵣ, w.2.1 * b, a₁, w.2.2 * b⟩

/-- The reduction's randomness for the slope pattern `w`: a uniform slope `b`, then
`twoDLEmbedAt`. -/
noncomputable def twoDLSampleEmbed (w : F × F × F) : ProbComp (TwoDLEmbed F) := do
  let b ← $ᵗ F
  twoDLEmbedAt w b

/-- The 2-DL reduction of O24 Claim 5.14 built from an algebraic one-more forger `A`, for the
slope pattern `w` (`twoDLSampleEmbed`, module docstring). `(1, 0, 0)` is the `x₀` case of the
paper. -/
noncomputable def omufTwoDLReductionAt (gen : G)
    [Fact (Function.Bijective (fun x : F => x • gen))]
    (A : AGMOMUFAdversary F G 1) (w : F × F × F) : QDLogAdversary 2 F G :=
  fun _ Xs => do
    let e ← twoDLSampleEmbed w
    let X := Xs 0
    let X' := Xs 1
    let pp := twoDLParams gen X e
    let (out, s) ← (simulateQ (twoDLImpl gen X X' e)
      (A.run (e.η • gen) pp)).run ([], [])
    let t : OMUFTrace F G := ⟨e.key 0, e.η • gen, pp, s.1, out⟩
    pure (twoDLExtract t gen X e (s.2.map Prod.fst))

/-- The mixture of three 2-DL adversaries: one of them, chosen uniformly and independently of the
challenge. -/
def twoDLMix (B₀ B₁ B₂ : QDLogAdversary 2 F G) : QDLogAdversary 2 F G :=
  fun g Xs => do
    let i ← $ᵗ (Fin 3)
    if i = 0 then B₀ g Xs else if i = 1 then B₁ g Xs else B₂ g Xs

end Reduction

section Coupling

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- The records of a log at the challenge `x`: `(u_j, x·V_j)` for each issued pair, `u_j` being the
logarithm of `U_j`. The reduction keeps them as it answers Sign, without knowing `x`. -/
noncomputable def twoDLAuxOf (x : F) (tags : List (G × G)) : List (F × G) :=
  tags.map fun t => (glog gen t.1, x • t.2)

/-- The multiples by `x` of the issued pairs, read off the records of a log. -/
lemma twoDLXTags_auxOf (x : F) (tags : List (G × G)) :
    twoDLXTags (x • gen) (twoDLAuxOf gen x tags) = tags.map fun t => (x • t.1, x • t.2) := by
  simp only [twoDLXTags, twoDLAuxOf, List.map_map]
  congr 1
  funext t
  simp only [Function.comp_apply, Prod.mk.injEq, and_true]
  rw [smul_comm, glog_smul]

omit hgen in
/-- Scaling a `zipWith` combination of issued pairs scales the pairs. -/
lemma smul_zipWith_sum_tags (x : F) (uv : List (F × F)) (tags : List (G × G)) :
    x • (List.zipWith (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2) uv tags).sum =
      (List.zipWith (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2) uv
        (tags.map fun t => (x • t.1, x • t.2))).sum := by
  induction tags generalizing uv with
  | nil => simp only [List.zipWith_nil_right, List.sum_nil, smul_zero, List.map_nil]
  | cons t ts ih =>
    cases uv with
    | nil => simp only [List.zipWith_nil_left, List.sum_nil, smul_zero]
    | cons c cs =>
      simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons, smul_add, ih]
      rw [smul_comm x c.1, smul_comm x c.2]

omit hgen in
/-- The public parameters of the reduction are those of the key at `x`. -/
lemma twoDLParams_eq (x : F) (e : TwoDLEmbed F) :
    twoDLParams gen (x • gen) e =
      ((e.key x).1 • (e.η • gen), (e.key x).2.1 • gen, fun i => (e.key x).2.2 i • gen) := by
  simp only [twoDLParams, TwoDLEmbed.key, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · module
  · module
  · funext i
    module

/-- The reduction's multiple by `x` of the element a representation names is `x` times it, at
the records of a log. -/
lemma twoDLxEval_eq (x : F) (e : TwoDLEmbed F) (ρ : AGMRepr F 1) (tags : List (G × G)) :
    twoDLxEval (x • gen) (x • (x • gen)) e ρ (twoDLAuxOf gen x tags) =
      x • ρ.eval gen (e.η • gen) (twoDLParams gen (x • gen) e).1
        (twoDLParams gen (x • gen) e).2.1 (twoDLParams gen (x • gen) e).2.2 tags := by
  simp only [twoDLxEval, AGMRepr.eval, twoDLXTags_auxOf, twoDLParams, smul_add,
    Finset.smul_sum, smul_zipWith_sum_tags]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 1
          · module
          · module
        · module
      · module
    · exact Finset.sum_congr rfl fun i _ => by module

omit hgen in
/-- The records of a log extended by an issued pair: the pair's own record, at the end. -/
lemma twoDLAuxOf_tags_append_some (x : F) (log : AGMOMUFLog F G 1) (C : G)
    (ρ : AGMRepr F 1) (p : G × G) :
    twoDLAuxOf gen x (AGMOMUFLog.tags (log ++ [(C, ρ, some p)])) =
      twoDLAuxOf gen x (AGMOMUFLog.tags log) ++ [(glog gen p.1, x • p.2)] := by
  simp only [AGMOMUFLog.tags_append_some, twoDLAuxOf, List.map_append, List.map_cons,
    List.map_nil]

omit hgen in
/-- A refused query leaves the records unchanged. -/
lemma twoDLAuxOf_tags_append_none (x : F) (log : AGMOMUFLog F G 1) (C : G)
    (ρ : AGMRepr F 1) :
    twoDLAuxOf gen x (AGMOMUFLog.tags (log ++ [(C, ρ, none)])) =
      twoDLAuxOf gen x (AGMOMUFLog.tags log) := by
  simp only [AGMOMUFLog.tags_append_none]

/-- The simulated `sign` answer, from the records of the log, is the real one, followed by the
records of the new log. -/
lemma twoDL_step_sign (secParam : ℕ) (x : F) (e : TwoDLEmbed F) (log : AGMOMUFLog F G 1)
    (C : G) (ρ : AGMRepr F 1) :
    (twoDLImpl gen (x • gen) (x • (x • gen)) e (.inr (.sign C ρ))).run
        (log, twoDLAuxOf gen x (AGMOMUFLog.tags log)) =
      (fun p : Option (G × G) × AGMOMUFLog F G 1 =>
          (p.1, (p.2, twoDLAuxOf gen x (AGMOMUFLog.tags p.2)))) <$>
        (agmOMUFImpl gen secParam (e.key x) (e.η • gen)
          (twoDLParams gen (x • gen) e) (.inr (.sign C ρ))).run log := by
  simp only [twoDLImpl, agmOMUFImpl, QueryImpl.add_apply_inr]
  simp only [twoDLOracleImpl, agmOMUFOracleImpl]
  simp only [StateT.run, StateT.mk]
  split_ifs with h
  · simp only [μCMZATCoreSyntax, atIssueSrv, bind_pure_comp, Functor.map_map, TwoDLEmbed.key]
    refine Eq.trans ?_ (Functor.map_map _ _ _).symm
    congr 1
    funext u
    have hV : e.a₀ • u • gen + (e.b₀ * u) • x • gen + u • (C + (e.aᵣ • gen + e.bᵣ • x • gen)) =
        (e.a₀ + e.b₀ * x) • u • gen + u • (C + (e.aᵣ + e.bᵣ * x) • gen) := by module
    have hxV : e.a₀ • u • x • gen + (e.b₀ * u) • x • x • gen +
          u • (x • C + (e.aᵣ • x • gen + e.bᵣ • x • x • gen)) =
        x • ((e.a₀ + e.b₀ * x) • u • gen + u • (C + (e.aᵣ + e.bᵣ * x) • gen)) := by module
    simp only [twoDLAuxOf_tags_append_some, glog_smul_self, twoDLxEval_eq, h.2, hV, hxV]
    rfl
  · change _ = pure _
    simp only [twoDLAuxOf_tags_append_none]
    rfl

/-- The simulated `verify` answer, from the records of the log, is the real one at the key
`e.key x`: on consistent representations `x·U` is the combination of the multiples by `x` of the
basis, so `V = (x₀ + xᵣ + m·x₁)·U` is `V = (a₀ + aᵣ + m·a₁)·U + (b₀ + bᵣ + m·b₁)·(x·U)`. -/
lemma twoDL_step_verify (secParam : ℕ) (x : F) (e : TwoDLEmbed F) (log : AGMOMUFLog F G 1)
    (m : Fin 1 → F) (σ : Code G) (ρU ρV : AGMRepr F 1) :
    (twoDLImpl gen (x • gen) (x • (x • gen)) e (.inr (.verify m σ ρU ρV))).run
        (log, twoDLAuxOf gen x (AGMOMUFLog.tags log)) =
      (fun p : Bool × AGMOMUFLog F G 1 =>
          (p.1, (p.2, twoDLAuxOf gen x (AGMOMUFLog.tags p.2)))) <$>
        (agmOMUFImpl gen secParam (e.key x) (e.η • gen)
          (twoDLParams gen (x • gen) e) (.inr (.verify m σ ρU ρV))).run log := by
  simp only [twoDLImpl, agmOMUFImpl, QueryImpl.add_apply_inr]
  simp only [twoDLOracleImpl, agmOMUFOracleImpl]
  simp only [StateT.run, StateT.mk]
  change _ = pure _
  rcases σ with ⟨U, V⟩
  by_cases hc : reprMatches ρU gen (e.η • gen) (twoDLParams gen (x • gen) e).1
        (twoDLParams gen (x • gen) e).2.1 (twoDLParams gen (x • gen) e).2.2
        (AGMOMUFLog.tags log) (U, V).1 ∧
      reprMatches ρV gen (e.η • gen) (twoDLParams gen (x • gen) e).1
        (twoDLParams gen (x • gen) e).2.1 (twoDLParams gen (x • gen) e).2.2
        (AGMOMUFLog.tags log) (U, V).2
  · have hx : twoDLxEval (x • gen) (x • (x • gen)) e ρU
        (twoDLAuxOf gen x (AGMOMUFLog.tags log)) = x • U := by
      rw [twoDLxEval_eq, hc.1.2]
    have hs : ((e.a₀ + e.b₀ * x) + (e.aᵣ + e.bᵣ * x) + (e.a₁ + e.b₁ * x) * m 0) • U =
        (e.a₀ + e.aᵣ + e.a₁ * m 0) • U + (e.b₀ + e.bᵣ + e.b₁ * m 0) • (x • U) := by
      module
    simp only [hx, μCMZATCoreSyntax, verify, macScalar, TwoDLEmbed.key, Fin.sum_univ_one, hs]
    rfl
  · simp only [hc, decide_false, Bool.false_and]
    rfl

omit hgen in
/-- A coin query leaves the log and the records unchanged, in the simulation and in the real
game. -/
lemma twoDL_step_coin (secParam : ℕ) (x : F) (e : TwoDLEmbed F) (log : AGMOMUFLog F G 1)
    (t : ℕ) :
    (twoDLImpl gen (x • gen) (x • (x • gen)) e (.inl t)).run
        (log, twoDLAuxOf gen x (AGMOMUFLog.tags log)) =
      (fun p : (unifSpec + AGMOMUFOracleSpec F G 1).Range (.inl t) × AGMOMUFLog F G 1 =>
          (p.1, (p.2, twoDLAuxOf gen x (AGMOMUFLog.tags p.2)))) <$>
        (agmOMUFImpl gen secParam (e.key x) (e.η • gen)
          (twoDLParams gen (x • gen) e) (.inl t)).run log := by
  simp only [twoDLImpl, agmOMUFImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
  simp [liftM, monadLift, MonadLift.monadLift, Functor.map_map]

/-- **The coupling.** At the key `e.key x`, the simulated run of any adversary from the log and its
records is the real run of the game followed by the records of the final log, an equality of
computations: the reduction answers every query as the game does. -/
theorem twoDL_run {α : Type} (secParam : ℕ) (x : F) (e : TwoDLEmbed F)
    (oa : OracleComp (unifSpec + AGMOMUFOracleSpec F G 1) α) (log : AGMOMUFLog F G 1) :
    (simulateQ (twoDLImpl gen (x • gen) (x • (x • gen)) e) oa).run
        (log, twoDLAuxOf gen x (AGMOMUFLog.tags log)) =
      (fun p : α × AGMOMUFLog F G 1 =>
          (p.1, (p.2, twoDLAuxOf gen x (AGMOMUFLog.tags p.2)))) <$>
        (simulateQ (agmOMUFImpl gen secParam (e.key x) (e.η • gen)
          (twoDLParams gen (x • gen) e)) oa).run log := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure y => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    rcases t with t | (⟨C, ρ⟩ | ⟨m, σ, ρU, ρV⟩)
    · rw [twoDL_step_coin gen secParam x e log t, bind_map_left]
      exact bind_congr fun p => ih _ _
    · rw [twoDL_step_sign gen secParam x e log C ρ]
      simp only [OracleSpec.add_apply_inr]
      refine (bind_map_left _ _ _).trans ?_
      rw [agmOMUFImpl_inr]
      exact bind_congr fun p => ih _ _
    · rw [twoDL_step_verify gen secParam x e log m σ ρU ρV]
      simp only [OracleSpec.add_apply_inr]
      refine (bind_map_left _ _ _).trans ?_
      rw [agmOMUFImpl_inr]
      exact bind_congr fun p => ih _ _

end Coupling

section KeyDistribution

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- A bijection fixing `0` pushes the uniform sample of the nonzero elements to that of the
other group. -/
lemma evalDist_map_uniformNonzero {A B : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Nontrivial A] [AddCommGroup B] [Fintype B] [DecidableEq B] [Nontrivial B]
    (f : A → B) (hf : Function.Bijective f) (h0 : f 0 = 0) :
    𝒟[f <$> uniformNonzero A] = 𝒟[uniformNonzero B] := by
  have hne : ∀ a : A, a ≠ 0 → f a ≠ 0 := fun a ha h => ha (hf.1 (h.trans h0.symm))
  let φ : {a : A // a ≠ 0} → {b : B // b ≠ 0} := fun a => ⟨f a.1, hne _ a.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a a' h => Subtype.ext (hf.1 (congrArg Subtype.val h)), fun b => ?_⟩
    obtain ⟨a, ha⟩ := hf.2 b.1
    refine ⟨⟨a, fun h0' => b.2 (ha ▸ h0' ▸ h0)⟩, Subtype.ext ha⟩
  haveI : Finite A := Finite.of_fintype A
  haveI : Finite {a : A // a ≠ 0} := Subtype.finite
  have h := evalDist_map_bijective_uniform_cross (α := {a : A // a ≠ 0})
    (β := {b : B // b ≠ 0}) φ hφ
  have e1 : uniformNonzero A = Subtype.val <$> ($ᵗ {a : A // a ≠ 0} : ProbComp _) := rfl
  have e2 : uniformNonzero B = Subtype.val <$> ($ᵗ {b : B // b ≠ 0} : ProbComp _) := rfl
  calc 𝒟[f <$> uniformNonzero A]
      = 𝒟[Subtype.val <$> (φ <$> ($ᵗ {a : A // a ≠ 0} : ProbComp _))] := by
        rw [e1, Functor.map_map, Functor.map_map]
    _ = Subtype.val <$> 𝒟[φ <$> ($ᵗ {a : A // a ≠ 0} : ProbComp _)] := evalDist_map _ _
    _ = Subtype.val <$> 𝒟[($ᵗ {b : B // b ≠ 0} : ProbComp _)] := by rw [h]
    _ = 𝒟[uniformNonzero B] := by rw [e2, evalDist_map]

/-- The crs of the reduction, `H = η·G` for `η` uniform among the nonzero scalars, is uniform
among the nonzero group elements, as `setup` draws it. -/
lemma evalDist_uniformUnits_smul_gen :
    𝒟[(fun η : F => η • gen) <$> uniformUnits F] = 𝒟[uniformNonzero G] := by
  unfold uniformUnits
  letI : AddCommGroup F := @Ring.toAddCommGroup F (@CommRing.toRing F Field.toCommRing)
  letI : Nontrivial F := DivisionRing.toNontrivial
  exact evalDist_map_uniformNonzero (fun η : F => η • gen) hgen.out (zero_smul F gen)

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A uniform sample that is not used changes nothing. -/
lemma evalDist_bind_uniform_const {γ : Type} (my : ProbComp γ) :
    𝒟[do let _ ← ($ᵗ F : ProbComp F); my] = 𝒟[my] := by
  apply evalDist_ext
  intro y
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]

/-- Bind congruence for evaluation distributions. -/
lemma evalDist_bind_congr' {α γ : Type} (mx : ProbComp α) {f g : α → ProbComp γ}
    (h : ∀ a, 𝒟[f a] = 𝒟[g a]) : 𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  rw [evalDist_bind, evalDist_bind]
  exact congrArg _ (funext h)

omit [DecidableEq F] in
/-- Shifting a uniform scalar by a constant does not change what a continuation sees. -/
lemma evalDist_bind_uniform_add_right {γ : Type} (c : F) (cont : F → ProbComp γ) :
    𝒟[do let a ← ($ᵗ F : ProbComp F); cont (a + c)] =
      𝒟[do let a ← ($ᵗ F : ProbComp F); cont a] := by
  have h := evalDist_bind_bijective_add_right_uniform (α := F) (β := F) id
    Function.bijective_id c cont
  simpa using h

omit [Fintype F] [DecidableEq F] in
/-- A uniform scalar shifted by a constant and read as a vector of length one is a uniform vector:
the last key component of the real key generation, `x ←$ F^1`. -/
lemma evalDist_bind_uniform_fin_one {γ : Type} (c : F) (cont : (Fin 1 → F) → ProbComp γ) :
    𝒟[do let a ← ($ᵗ F : ProbComp F); cont (fun _ => a + c)] =
      𝒟[do let v ← ($ᵗ (Fin 1 → F) : ProbComp (Fin 1 → F)); cont v] := by
  have hbij : Function.Bijective (fun (a : F) (_ : Fin 1) => a) :=
    ⟨fun a b h => congrFun h 0, fun v => ⟨v 0, funext fun i => by rw [Subsingleton.elim i 0]⟩⟩
  exact evalDist_bind_bijective_add_right_uniform (α := F) (β := Fin 1 → F) (fun a _ => a) hbij
    (fun _ => c) cont

/-- The crs and the key of the real game, `(H, sk)`: `H` from `setup`, then `keygen`. -/
noncomputable def omufCrsKey (gen : G) (secParam : ℕ) : ProbComp (G × Key F 1) := do
  let H ← (μCMZATCoreSyntax F gen).setup secParam 1
  let (sk, _) ← (μCMZATCoreSyntax F gen).keygen (secParam := secParam) (n := 1) H
  pure (H, sk)

/-- **The slope is perfectly hidden by the offsets** (the step of O24 Claims 5.12 to 5.14, p. 46,
"`b` is uniformly distributed and perfectly hidden by `a`"). At every slope `b`, whatever it is,
including `0`, the crs and the key the reduction presents, `(η·G, e.key x)`, have the
distribution of the real game: the slope times `x` only shifts the offsets, which are uniform, and
`η·G` for `η` uniform among the nonzero scalars is the nonzero crs of `setup`. So the view does not
depend on `b`. -/
theorem twoDLEmbedAt_key (secParam : ℕ) (w : F × F × F) (x b : F) :
    𝒟[(fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLEmbedAt w b] =
      𝒟[omufCrsKey (F := F) gen secParam] := by
  -- The real side is the nonzero crs and three uniform key components.
  have hreal : omufCrsKey (F := F) gen secParam =
      (do
        let H ← uniformNonzero G
        let x₀ ← ($ᵗ F : ProbComp F)
        let xᵣ ← ($ᵗ F : ProbComp F)
        let v ← ($ᵗ (Fin 1 → F) : ProbComp (Fin 1 → F))
        pure (H, (x₀, xᵣ, v))) := by
    simp only [omufCrsKey, μCMZATCoreSyntax, μCMZBaseMACSyntax, setup, keygen, bind_assoc,
      pure_bind]
  rw [hreal]
  simp only [twoDLEmbedAt, map_bind, map_pure, TwoDLEmbed.key]
  -- The offsets absorb the slopes' contributions.
  have hrest : ∀ (η c₀ c₁ c₂ : F),
      𝒟[do
        let a₂ ← ($ᵗ F : ProbComp F)
        let a₃ ← ($ᵗ F : ProbComp F)
        let a₄ ← ($ᵗ F : ProbComp F)
        pure (η • gen, a₂ + c₀, a₃ + c₁, fun _ => a₄ + c₂)] =
      𝒟[do
        let x₀ ← ($ᵗ F : ProbComp F)
        let xᵣ ← ($ᵗ F : ProbComp F)
        let v ← ($ᵗ (Fin 1 → F) : ProbComp (Fin 1 → F))
        pure (η • gen, x₀, xᵣ, v)] := by
    intro η c₀ c₁ c₂
    refine (evalDist_bind_congr' _ fun a₂ => evalDist_bind_congr' _ fun a₃ =>
      evalDist_bind_uniform_fin_one c₂ (fun v => pure (η • gen, a₂ + c₀, a₃ + c₁, v))).trans ?_
    refine (evalDist_bind_congr' _ fun a₂ =>
      evalDist_bind_uniform_add_right c₁ (fun r => (do
        let v ← ($ᵗ (Fin 1 → F) : ProbComp (Fin 1 → F))
        pure (η • gen, a₂ + c₀, r, v) : ProbComp _))).trans ?_
    exact evalDist_bind_uniform_add_right c₀ (fun r => (do
      let xᵣ ← ($ᵗ F : ProbComp F)
      let v ← ($ᵗ (Fin 1 → F) : ProbComp (Fin 1 → F))
      pure (η • gen, r, xᵣ, v) : ProbComp _))
  -- The nonzero crs.
  have hcrs : ∀ K : G → ProbComp (G × Key F 1),
      𝒟[do let η ← uniformUnits F; K (η • gen)] = 𝒟[do let H ← uniformNonzero G; K H] := by
    intro K
    have h : (do let η ← uniformUnits F; K (η • gen)) =
        ((fun η : F => η • gen) <$> uniformUnits F) >>= K := by simp [monad_norm]
    rw [h, evalDist_bind, evalDist_uniformUnits_smul_gen gen, ← evalDist_bind]
  refine (evalDist_bind_congr' _ fun η =>
    hrest η (w.1 * b * x) (w.2.1 * b * x) (w.2.2 * b * x)).trans ?_
  exact hcrs fun H => (do
    let x₀ ← ($ᵗ F : ProbComp F)
    let xᵣ ← ($ᵗ F : ProbComp F)
    let v ← ($ᵗ (Fin 1 → F) : ProbComp (Fin 1 → F))
    pure (H, x₀, xᵣ, v) : ProbComp _)

/-- The slope is independent of the view: the joint distribution of the slope and of the crs and
key the reduction presents is the product of the uniform slope and the real view. The degenerate
mask of the paper, `b = 0`, has probability `1/p` (`probOutput_uniformSample`) and does not
change the view. -/
theorem twoDLEmbedAt_indep (secParam : ℕ) (w : F × F × F) (x : F) :
    𝒟[do
      let b ← ($ᵗ F : ProbComp F)
      let e ← twoDLEmbedAt w b
      pure (b, e.η • gen, e.key x)] =
    𝒟[do
      let b ← ($ᵗ F : ProbComp F)
      let r ← omufCrsKey (F := F) gen secParam
      pure (b, r)] := by
  refine evalDist_bind_congr' _ fun b => ?_
  have hl : (do let e ← twoDLEmbedAt w b; pure (b, e.η • gen, e.key x) : ProbComp _) =
      Prod.mk b <$> ((fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLEmbedAt w b) := by
    simp [monad_norm]
  have hr : (do let r ← omufCrsKey (F := F) gen secParam; pure (b, r) : ProbComp _) =
      Prod.mk b <$> omufCrsKey (F := F) gen secParam := by
    simp [monad_norm]
  rw [hl, hr]
  calc 𝒟[Prod.mk b <$> ((fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLEmbedAt w b)]
      = Prod.mk b <$> 𝒟[(fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLEmbedAt w b] :=
        evalDist_map _ _
    _ = Prod.mk b <$> 𝒟[omufCrsKey (F := F) gen secParam] := by
        rw [twoDLEmbedAt_key gen secParam w x b]
    _ = 𝒟[Prod.mk b <$> omufCrsKey (F := F) gen secParam] := (evalDist_map _ _).symm

/-- The crs and the key the reduction presents, over its whole randomness, have the distribution
of the real game, for every slope pattern and every challenge: the slope averages out of
`twoDLEmbedAt_key`. -/
theorem twoDLSampleEmbed_key (secParam : ℕ) (w : F × F × F) (x : F) :
    𝒟[(fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLSampleEmbed w] =
      𝒟[omufCrsKey (F := F) gen secParam] := by
  have h : (fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLSampleEmbed w =
      (do let b ← ($ᵗ F : ProbComp F);
          (fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLEmbedAt w b) := by
    simp [twoDLSampleEmbed, monad_norm]
  rw [h]
  refine (evalDist_bind_congr' _ fun b => twoDLEmbedAt_key gen secParam w x b).trans ?_
  exact evalDist_bind_uniform_const _

end KeyDistribution

section TraceLevel

variable (gen : G) [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- The public parameters of the key `sk` at the crs `H`, as `keygen` computes them. -/
def omufParams (H : G) (sk : Key F 1) : Params G 1 :=
  (sk.1 • H, sk.2.1 • gen, fun i => sk.2.2 i • gen)

/-- The run of the game from a fixed crs and key, as `agmOMUFTrace` makes it after key
generation. -/
noncomputable def omufTraceFrom (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (H : G)
    (sk : Key F 1) : ProbComp (OMUFTrace F G) := do
  let (out, log) ← (simulateQ (agmOMUFImpl gen secParam sk H (omufParams gen H sk))
    (A.run H (omufParams gen H sk))).run []
  pure ⟨sk, H, omufParams gen H sk, log, out⟩

omit hgen in
/-- The trace is the run from the crs and the key of the real game. -/
theorem agmOMUFTrace_eq (secParam : ℕ) (A : AGMOMUFAdversary F G 1) :
    agmOMUFTrace gen secParam A =
      (omufCrsKey (F := F) gen secParam >>= fun r => omufTraceFrom gen secParam A r.1 r.2) := by
  simp only [agmOMUFTrace, omufCrsKey, omufTraceFrom, omufParams, agmOMUFImpl, μCMZATCoreSyntax,
    μCMZBaseMACSyntax, setup, keygen, bind_assoc, pure_bind]

/-- The reduction's run at the challenge `x`, before extraction: its randomness, the forger's
output and the final state, simulating the forger from the empty log. -/
noncomputable def twoDLRunAt (A : AGMOMUFAdversary F G 1) (w : F × F × F) (x : F) :
    ProbComp (TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G) := do
  let e ← twoDLSampleEmbed w
  let (out, s) ← (simulateQ (twoDLImpl gen (x • gen) (x • (x • gen)) e)
    (A.run (e.η • gen) (twoDLParams gen (x • gen) e))).run ([], [])
  pure (e, out, s)

/-- The trace of a run of the reduction: the key at the challenge, the crs and the public parameters
the reduction presented, the log, and the forger's output. -/
def twoDLTraceOf (x : F) (r : TwoDLEmbed F × List (AGMOMUFForgery F G 1) × TwoDLState F G) :
    OMUFTrace F G :=
  ⟨r.1.key x, r.1.η • gen, twoDLParams gen (x • gen) r.1, r.2.2.1, r.2.1⟩

/-- **The trace of the reduction's run is the trace of the game.** At every challenge `x`, the
simulated run of the forger, read as a trace, has the distribution of `agmOMUFTrace`: the crs and
the key are the real ones (`twoDLSampleEmbed_key`) and the simulated oracles answer as the real
ones (`twoDL_run`). -/
theorem twoDLRunAt_trace (secParam : ℕ) (A : AGMOMUFAdversary F G 1) (w : F × F × F) (x : F) :
    𝒟[twoDLTraceOf gen x <$> twoDLRunAt gen A w x] = 𝒟[agmOMUFTrace gen secParam A] := by
  have h0 : twoDLAuxOf gen x (AGMOMUFLog.tags ([] : AGMOMUFLog F G 1)) = [] := rfl
  -- For each randomness, the simulated run is the real run from that crs and key.
  have hrun : ∀ e : TwoDLEmbed F,
      𝒟[twoDLTraceOf gen x <$> (do
        let (out, s) ← (simulateQ (twoDLImpl gen (x • gen) (x • (x • gen)) e)
          (A.run (e.η • gen) (twoDLParams gen (x • gen) e))).run ([], [])
        pure (e, out, s))] = 𝒟[omufTraceFrom gen secParam A (e.η • gen) (e.key x)] := by
    intro e
    have h := twoDL_run gen secParam x e (A.run (e.η • gen) (twoDLParams gen (x • gen) e)) []
    rw [h0] at h
    rw [twoDLParams_eq gen x e] at h ⊢
    rw [h]
    congr 1
    simp only [omufTraceFrom, omufParams, twoDLTraceOf, TwoDLEmbed.key, bind_pure_comp,
      Functor.map_map, twoDLParams_eq gen x e]
  -- Average over the reduction's randomness.
  have hmap : twoDLTraceOf gen x <$> twoDLRunAt gen A w x =
      (twoDLSampleEmbed w >>= fun e => twoDLTraceOf gen x <$> (do
        let (out, s) ← (simulateQ (twoDLImpl gen (x • gen) (x • (x • gen)) e)
          (A.run (e.η • gen) (twoDLParams gen (x • gen) e))).run ([], [])
        pure (e, out, s))) := by
    simp only [twoDLRunAt, map_bind]
  rw [hmap]
  refine (evalDist_bind_congr' _ hrun).trans ?_
  have hview : (twoDLSampleEmbed w >>= fun e =>
        omufTraceFrom gen secParam A (e.η • gen) (e.key x)) =
      ((fun e : TwoDLEmbed F => (e.η • gen, e.key x)) <$> twoDLSampleEmbed w) >>=
        fun r => omufTraceFrom gen secParam A r.1 r.2 := by
    simp [monad_norm]
  rw [hview, evalDist_bind, twoDLSampleEmbed_key gen secParam w x, ← evalDist_bind,
    agmOMUFTrace_eq]

end TraceLevel

section Mixture

/-- The advantage of the three-way mixture is the mean of the three advantages:
`3·Adv(mixture) = Adv(B₀) + Adv(B₁) + Adv(B₂)`, the factor `3` of Claim 5.14. -/
theorem qdlogAdv_twoDLMix (gen : G) (B₀ B₁ B₂ : QDLogAdversary 2 F G) :
    (3 : ℝ≥0∞) * qdlogAdv 2 gen (twoDLMix B₀ B₁ B₂) =
      qdlogAdv 2 gen B₀ + qdlogAdv 2 gen B₁ + qdlogAdv 2 gen B₂ := by
  have h : qdlogAdv 2 gen (twoDLMix B₀ B₁ B₂) =
      ∑ i : Fin 3, (3 : ℝ≥0∞)⁻¹ *
        (if i = 0 then qdlogAdv 2 gen B₀ else if i = 1 then qdlogAdv 2 gen B₁
          else qdlogAdv 2 gen B₂) := by
    unfold qdlogAdv
    simp only [qdlogExp, twoDLMix, bind_assoc]
    rw [probOutput_bind_bind_swap, probOutput_bind_eq_sum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [probOutput_uniformSample, Fintype.card_fin]
    push_cast
    congr 1
    by_cases hi0 : i = 0
    · simp [hi0]
    · by_cases hi1 : i = 1 <;> simp [hi0, hi1]
  rw [h, Fin.sum_univ_three]
  simp only [Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc _ = ((3 : ℝ≥0∞) * 3⁻¹) * (qdlogAdv 2 gen B₀ + qdlogAdv 2 gen B₁ + qdlogAdv 2 gen B₂) := by
        ring
    _ = _ := by rw [h3, one_mul]

end Mixture

end KVAC.Schemes.MicroCMZ
