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
forger `A` (`omufTwoDLReductionAt`). Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of
item 17.

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
of case independent of the challenge (`twoDLMix`, a `uniformMix`), so that `3·Adv(mixture)` is the
sum of the three advantages (`qdlogAdv_twoDLMix`), the factor `3` of Claim 5.14.
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

/-- The reduction's answers to the two oracle arms, without the key. An issuance nonce `u_j` is
drawn with `uniformUnits`, from the nonzero scalars, as in the game (DA *Nonzero issuance nonces*,
item A3.2 of `docs/findings/FINDINGS_AND_LESSONS.md`). -/
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
  let pt := AGMPoly.spec (Polynomial.C e.η)
    (Polynomial.C e.a₀ + Polynomial.C e.b₀ * Polynomial.X)
    (Polynomial.C e.aᵣ + Polynomial.C e.bᵣ * Polynomial.X)
    (Polynomial.C e.a₁ + Polynomial.C e.b₁ * Polynomial.X)
    fun j : Fin t.arity => Polynomial.C (us.getD j 0)
  match (t.forgeryPolys.map fun φ => pt φ).find? (fun p => decide (p ≠ 0)) with
  | some p => (p.roots.toList.find? fun r => decide (r • g = X)).getD 0
  | none => 0

end Extraction

section Reduction

/-- The 2-DL reduction of O24 Claim 5.14 built from an algebraic one-more forger `A`, for the
slope pattern `w`: the key variable with weight `1` gets the slope `b`, the others slope `0`
(module docstring). `(1, 0, 0)` is the `x₀` case of the paper.

The paper samples `η` and the issuance nonces `u_j` from `ℤ_p` (p. 47). The reduction draws `η`
here, and `u_j` in `twoDLOracleImpl`, with `uniformUnits`, from the nonzero scalars, as the game
does: the crs `H = η • G` is nonzero (DA *Nonzero crs H*, item A3.3 of
`docs/findings/FINDINGS_AND_LESSONS.md`) and so are the nonces (DA *Nonzero issuance nonces*,
item A3.2 of the same file). -/
noncomputable def omufTwoDLReductionAt (gen : G)
    [Fact (Function.Bijective (fun x : F => x • gen))]
    (A : AGMOMUFAdversary F G 1) (w : F × F × F) : QDLogAdversary 2 F G :=
  fun _ Xs => do
    let η ← uniformUnits F
    let a₀ ← $ᵗ F
    let aᵣ ← $ᵗ F
    let a₁ ← $ᵗ F
    let b ← $ᵗ F
    let e : TwoDLEmbed F := ⟨η, a₀, w.1 * b, aᵣ, w.2.1 * b, a₁, w.2.2 * b⟩
    let X := Xs 0
    let X' := Xs 1
    let pp := twoDLParams gen X e
    let (out, s) ← (simulateQ (twoDLImpl gen X X' e)
      (A.run (e.η • gen) pp)).run ([], [])
    let t : OMUFTrace F G := ⟨e.key 0, e.η • gen, pp, s.1, out⟩
    pure (twoDLExtract t gen X e (s.2.map Prod.fst))

/-- The uniform mixture of `k` adversaries: `B i` for an index `i` drawn uniformly from `Fin k`,
independently of the challenge. -/
def uniformMix {α β γ : Type} (k : ℕ) [NeZero k] (B : Fin k → α → β → ProbComp γ) :
    α → β → ProbComp γ :=
  fun a b => do
    let i ← $ᵗ (Fin k)
    B i a b

/-- The mixture of three 2-DL adversaries: one of them, chosen uniformly and independently of the
challenge (`uniformMix` at `k = 3`). -/
def twoDLMix (B₀ B₁ B₂ : QDLogAdversary 2 F G) : QDLogAdversary 2 F G :=
  uniformMix 3 ![B₀, B₁, B₂]

end Reduction

section Mixture

/-- The success probability of a uniform mixture against any experiment that samples a challenge
`s`, runs the adversary on an input `inp s` and checks its output against `s`: `k` times it is the
sum of the success probabilities of the `k` adversaries. -/
theorem probOutput_uniformMix {σ α β γ : Type} (k : ℕ) [NeZero k]
    (B : Fin k → α → β → ProbComp γ) (mx : ProbComp σ) (a : α) (inp : σ → β)
    (check : σ → γ → Bool) :
    (k : ℝ≥0∞) * Pr[= true | do
        let s ← mx
        let y ← uniformMix k B a (inp s)
        return check s y] =
      ∑ i, Pr[= true | do
        let s ← mx
        let y ← B i a (inp s)
        return check s y] := by
  have h : Pr[= true | do
        let s ← mx
        let y ← uniformMix k B a (inp s)
        return check s y] =
      ∑ i : Fin k, (k : ℝ≥0∞)⁻¹ * Pr[= true | do
        let s ← mx
        let y ← B i a (inp s)
        return check s y] := by
    simp only [uniformMix, bind_assoc]
    rw [probOutput_bind_bind_swap, probOutput_bind_eq_sum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [probOutput_uniformSample, Fintype.card_fin]
  rw [h, ← Finset.mul_sum, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne k) (ENNReal.natCast_ne_top k), one_mul]

/-- The advantage of the three-way mixture is the mean of the three advantages:
`3·Adv(mixture) = Adv(B₀) + Adv(B₁) + Adv(B₂)`, the factor `3` of Claim 5.14. -/
theorem qdlogAdv_twoDLMix (gen : G) (B₀ B₁ B₂ : QDLogAdversary 2 F G) :
    (3 : ℝ≥0∞) * qdlogAdv 2 gen (twoDLMix B₀ B₁ B₂) =
      qdlogAdv 2 gen B₀ + qdlogAdv 2 gen B₁ + qdlogAdv 2 gen B₂ := by
  have h := probOutput_uniformMix 3 ![B₀, B₁, B₂] ($ᵗ F) gen
    (fun x (i : Fin 2) => (x ^ ((i : ℕ) + 1)) • gen) (fun x y => decide (y = x))
  rw [Fin.sum_univ_three] at h
  exact_mod_cast h

end Mixture

end KVAC.Schemes.MicroCMZ
