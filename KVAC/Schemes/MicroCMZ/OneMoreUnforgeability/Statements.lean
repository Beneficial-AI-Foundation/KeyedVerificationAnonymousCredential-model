/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.CaseEvents
import KVAC.Preliminaries.Assumptions
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.GapDLReduction
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Bridge
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.TwoDLExtraction
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.TwoDLReduction
import VCVio.OracleComp.QueryTracking.QueryBound
import KVAC.Schemes.MicroCMZ.AGMReduction.AttributeCollapse

/-!
# μCMZ_AT one-more unforgeability — the Theorem 5.11 target statements (O24 §5.6)

Theorem 5.11 of Orrù, *Revisiting Keyed-Verification Anonymous Credentials*
(IACR ePrint 2024/1552), for the μCMZ_AT core in the AGM-instrumented game of
`OneMoreUnforgeability/Game.lean`: at `n = 1` (Equation 23), the
case the paper proves directly, for every `n` (the printed bound), and the
Claims 5.12 to 5.14 of the `n = 1` proof over the case events of
`CaseEvents.lean`. Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of
item 17 (issue #189). Stated first and `sorry`d on the pattern of
`AGMReduction/SecurityN1.lean`, so that the reductions review against visible
targets; the blueprint nodes `mucmz_at_agm_omuf_n1`, `mucmz_at_agm_omuf` and
`omuf_case_i` to `omuf_case_iii` show "contains sorry" until the proofs are
merged.

## The statements and their parts

  agm_omuf_le_n1 :  AGM_OMUFAdv gen A secParam  ≤  omufBoundN1 F q εdl ε2dl
                    for every  A : AGMOMUFAdversary F G 1
  agm_omuf_le    :  AGM_OMUFAdv gen A secParam  ≤  omufBound F q εdl' ε2dl' εgap
                    for every  0 < n  and  A : AGMOMUFAdversary F G n
    both under the budget hypothesis
      ∀ H pp, IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q     at most q Sign queries,
                                                                    refused ones included
    where
      omufBoundN1 F q εdl ε2dl    = (q + 4)/p + (q + 1)·εdl + 3·ε2dl         Equation 23
      omufBound F q εdl ε2dl εgap = (q + 6)/p + (q + 1)·εdl + 3·ε2dl + εgap  printed bound
      εdl  = dlogAdv gen (omufDLReduction gen q A)        DL reduction, the mixture of the
                                                          two Claim reductions below
      ε2dl = twoDlogAdv gen (omufTwoDLReduction gen A)    2-DL reduction, Claim 5.14
                                                          (x₀, xᵣ, x₁ monomials, three cases)
      εdl', ε2dl'  the same two at the transformed adversary  omufToN1 gen A
                                                          attribute lifting, distinct case
      εgap = gapDlogAdv gen (omufGapDLReduction gen A)    collision case
    with the paper's printed constants, provisional.

  omuf_claim_5_12 :  Pr[ CaseU   | agmOMUFTrace gen secParam A ]  ≤  q·(1/p + εU)     item (i)
  omuf_claim_5_13 :  Pr[ CaseEta | agmOMUFTrace gen secParam A ]  ≤  1/p + εη         item (ii)
  omuf_claim_5_14 :  Pr[ CaseX   | agmOMUFTrace gen secParam A ]  ≤  3·(1/p + ε2dl) + εdeg
                                                                                      item (iii)
    for every  A : AGMOMUFAdversary F G 1,  over the case events of CaseEvents.lean,
    the first under the budget hypothesis, the other two without
    where
      εU = dlogAdv gen (omufDLReductionU gen q A)         Claim 5.12, selector over ι ∈ [q]
      εη = dlogAdv gen (omufDLReductionEta gen A)         Claim 5.13, challenge in the crs
    and the theorem's εdl is the mixture  q/(q + 1)·εU + 1/(q + 1)·εη,  so that
      q·(1/p + εU) + (1/p + εη) + 3·(1/p + ε2dl)  =  omufBoundN1 F q εdl ε2dl
    once the win is covered by the three events (pigeonhole, proof phase). Each Claim carries an
    extra term, the probability that the extraction of its reduction has nothing to extract
    (`TwoDLExtraction.lean`): εdegU = omufDegenerateProbU, εdegη = omufDegenerateProbEta and
    εdeg = omufDegenerateProb, for Claims 5.12, 5.13 and 5.14. The paper treats them as `0`,
    which is false as stated (below), so `agm_omuf_le_n1` carries their sum
    `omufDegenerateProbAll`, and `agm_omuf_le` carries it at the transformed adversary.

Sign is Figure 6's name for the MAC code generation oracle in the token setting,
and the name of the Lean constructor and of the budget predicate
`AGMOMUFQuery.isSign`. This file keeps it, as `Game.lean` and
`KVAC.Preliminaries.AnonymousTokens.Security` do.

The `n = 1` case is the one the paper proves directly. General `n` follows from
it (p. 46): the winning event splits by whether the forgeries' attribute
combinations `Σᵢ mᵢ·Xᵢ` are pairwise distinct, the distinct case reduces to
`n = 1` on a transformed adversary, and the colliding case to gap-DL by an
argument in the style of Lemma 5.5 (which the paper's text cites as Theorem
5.5). The six named constructions, the theorem's two reductions, the two
per-Claim discrete-log reductions, the attribute-lifting transformation
`omufToN1 : AGMOMUFAdversary F G n → AGMOMUFAdversary F G 1`, and the gap-DL
reduction `omufGapDLReduction`: the gap-DL reduction is built in `GapDLReduction.lean` and
the transformation `omufToN1` is built below, sampling the scaling scalars through the
private coin oracle and collapsing queries and forgeries along them. The other four are
declared with `sorry` bodies, the first sorried definitions in the repository, and are built
with the proofs of the Claims over the polynomial layer of Equations 17 to 22
(`Polynomial.lean`, `CaseEvents.lean`). Whether the transformation reuses the Lemma 5.5
embedding of the MAC track is open with Semar (question C2 of the Theorem 5.3 plan). The
adversary has a private coin oracle (`Game.lean`, *The adversary has a private coin oracle*),
so a transformation that needs randomness samples through it. Extra Sign queries are
not a source of randomness, they break the budget and the one-more count.

## Why named reductions

The hardness assumptions of `KVAC.Preliminaries.Assumptions` give the advantage
of one concrete adversary, `dlogAdv gen B`, and no scalar "best possible
advantage", so the paper's `Adv^dl` must be read as the advantage of the
reduction built from `A`, and the statement must name it. The two ways of not
naming it fail at fixed parameters: a perfect discrete-log solver exists as a
function of the finite group, with advantage `1`, so quantifying existentially
over the reductions is vacuous (the right-hand side exceeds every probability),
and assuming a bound `ε` on every discrete-log adversary is false below `1` and
trivial at or above it. Hence the shape of `agm_ufcmva_le_n1_explicit` against
named reductions. Their `sorry` sits at the whole function type, not under
the binders, so that the placeholders are not definitionally independent of
their arguments (a `def … (A) := sorry` would make `f A₁ = f A₂` hold by `rfl`).
No lemma may be stated about them beyond the theorems and Claims of this file
until they are built,
since anything provable about an unspecified body holds of every inhabitant. The
discrete-log reductions of the theorem and of Claim 5.12 take the budget `q`,
since a selector over the `q` issuance positions needs it. Claim 5.13's embeds
the challenge in the crs and the 2-DL reduction selects among three fixed
cases, so neither takes it.

## Constants and the extraction obligation

`omufBoundN1` carries the printed constants of Equation 23, provisional: the
repository already documents one Schwartz–Zippel undercount in this section
family (`3/p` for a printed `1/p`, `AGMPolynomial.lean`), and the Claims share
the pattern. The constant audit of the proof phase settles them, with an errata
item on any change, and the named definitions make such a change one line each.
The printed general bound `omufBound` exceeds Equation 23 by `2/p + Adv^gapdl`,
the overhead the paper attributes to the general `n` argument as a whole, "by
Theorem 5.5" (p. 46), without assigning it to the two cases.

The crs. `setup` of the base MAC draws `H` from the nonzero elements of `G`
(`uniformNonzero`, the first action of #149; it previously drew `H` uniformly
from `G`). The statements type-check unchanged and bound the game with
`H ←$ 𝔾×`. Oana's proof-level estimate of the change in advantage is
`(q + 3)/(p(p − 1))`, and the black-box transfer bounds it by `1/p`. The
reductions that embed the challenge in the crs, `omufDLReductionEta` and
`omufTwoDLReduction`, draw their `H` conditioned on `H ≠ 0`, as the 3-DL
reduction of Lemma 5.4 does since #149, so that the reduction's crs has the
game's law.

The paper's `1/p` in each Claim is the degenerate mask, `b = 0` or the
substituted polynomial in `χ` trivial, `b` uniform and hidden by `a`. A second
event sits between the case events and the extraction. The events are the
paper's items, a nonzero monomial in the variable of a formal polynomial, while
the reduction extracts from the univariate polynomial left after evaluating
every other variable at the run's values, and the monomial's coefficient, a
nonzero polynomial in those other variables, can vanish there
(issue #251; errata item 12 of
`docs/presentations/rolf-status/errata.md` offers the disjunction of a term of
about `Q/p` and a route to the `x₀` embedding). Two forgers, both by hand
arguments and not checked in Lean:

- Claim 5.13. With no Sign query, `Q < p` Verify queries `(0, (G, c·G))` over
  distinct `c` and a final guess among the untested values, a forger learns
  `k = x₀ + xᵣ` with probability `(Q + 1)/p` and outputs `(0, (H, k·H))`
  represented over `H`, which wins whenever `k` is right and `H ≠ 0`. Its
  polynomial `η·(x₀ + xᵣ − k)` has an `η` monomial, so `CaseEta` holds, yet on
  every win it vanishes identically once `η` is replaced by `a + b·χ`, so the
  Claim 5.13 reduction has nothing to extract. (`(Q + 1)/p` is for `H` drawn
  from the nonzero elements, as here; for `H` uniform in `G` it is
  `(Q + 1)(p − 1)/p²`.) This refutes the extraction step, not the displayed
  bound of Claim 5.13, which would need a bound on the vanishing event.
- Claim 5.14. With no query at all, a forger guesses `g` and outputs
  `(m, (H, X₀ + g·(Xᵣ + m·X₁)))` with `m ≠ 0`. Since `X₀ = x₀·H` has logarithm
  `η·x₀`, its polynomial is `(g − η)(xᵣ + m·x₁)`, with monomials in `xᵣ` and `x₁`. It
  wins when `g = η`, with probability about `1/(p − 1)`, where the polynomial
  vanishes identically in `xᵣ` and in `x₁`. For `x₀`, a forger guesses `h` and outputs
  `(m, (gen, h·X₀ + Xᵣ + m·X₁))`, with polynomial `(h·η − 1)·x₀`, which wins and vanishes
  identically in `x₀` when `h·η = 1`. So the vanishing probability the paper takes to be `0`
  is positive for each of the three cases.

Schwartz–Zippel bounds such a vanishing by `d/p` only for a polynomial
independent of the run's values, and honest Verify answers break that
independence, each being a test of the key, with no Verify budget in the game.
The Claims therefore carry the vanishing probability as an explicit term
(`omufDegenerateProbU`, `omufDegenerateProbEta`, `omufDegenerateProb`, `TwoDLExtraction.lean`),
and `agm_omuf_le_n1` and `agm_omuf_le` with them. Claims 5.12 and 5.13 are `sorry`d, with the
term in their statements as in the proved Claim 5.14. Whether the
Claims keep the paper's events, with a covering argument that assigns every
winning polynomial to a reduction that extracts from it, or move to evaluated
events, and whether a Verify budget and a per-Verify-query term join the
statements, is an obligation of the proof phase beyond the constant audit, and
a decision of the Theorem 5.3 plan. None of this shows the paper's displayed
bounds or Theorem 5.11 false. The paper's own item list (p. 45) cites the
three Claims as Theorems 5.12 to 5.14.

## Out of scope

The plain Figure 6 game (the OMUF analogue of the MAC track's #81 bridge), the
`π_is`-carrying variant and its lifting lemma (items 18 and 17b), and any proof.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

/-! ## The bound -/

/--
The Equation 23 bound of O24 Theorem 5.11 at `n = 1`,
`(q + 4)/p + (q + 1)·εdl + 3·ε2dl`, for `q` Sign queries, `p = |F|`, and the
discrete-log and 2-DL advantages `εdl`, `ε2dl` of the reductions. Printed
constants, provisional until the Track CMZ-OMUF constant audit (module
docstring, *Constants*).
-/
noncomputable def omufBoundN1 (F : Type) [Fintype F] (q : ℕ) (εdl ε2dl : ℝ≥0∞) :
    ℝ≥0∞ :=
  ((q : ℝ≥0∞) + 4) * (Fintype.card F : ℝ≥0∞)⁻¹ + ((q : ℝ≥0∞) + 1) * εdl +
    3 * ε2dl

/-- The three Claims' bounds add up to Equation 23, given that the discrete-log advantage of the
theorem's reduction is the mixture of the two Claim advantages: `(q + 1)·εdl = q·εU + εη`. -/
theorem omufBoundN1_eq_of_mix (F : Type) [Fintype F] (q : ℕ) (εU εη εdl ε2dl : ℝ≥0∞)
    (h : ((q : ℝ≥0∞) + 1) * εdl = (q : ℝ≥0∞) * εU + εη) :
    (q : ℝ≥0∞) * ((Fintype.card F : ℝ≥0∞)⁻¹ + εU) +
        (((Fintype.card F : ℝ≥0∞)⁻¹ + εη) + 3 * ((Fintype.card F : ℝ≥0∞)⁻¹ + ε2dl)) =
      omufBoundN1 F q εdl ε2dl := by
  unfold omufBoundN1
  rw [add_assoc _ (((q : ℝ≥0∞) + 1) * εdl), h]
  ring

/--
The printed bound of O24 Theorem 5.11 for every `n`,
`(q + 6)/p + (q + 1)·εdl + 3·ε2dl + εgap`, with `εgap` the gap-DL advantage of
the collision-case reduction. Exceeds `omufBoundN1` by `2/p + εgap`, the paper's
total for the general `n` argument (p. 46, "by Theorem 5.5"), not split between
its two cases. Printed constants, provisional (module docstring, *Constants*).
-/
noncomputable def omufBound (F : Type) [Fintype F] (q : ℕ) (εdl ε2dl εgap : ℝ≥0∞) :
    ℝ≥0∞ :=
  ((q : ℝ≥0∞) + 6) * (Fintype.card F : ℝ≥0∞)⁻¹ + ((q : ℝ≥0∞) + 1) * εdl +
    3 * ε2dl + εgap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

/-! ## The reductions, named now and built with the proofs

The generator and its bijectivity fact are explicit binders here rather than
section variables, since a `sorry` body mentions neither and a section variable
joins a definition only when mentioned. The `sorry` inhabits the whole function
type (module docstring, *Why named reductions*). -/

/--
The discrete-log reduction of O24 Claim 5.12 (item (i), a `u_ι` monomial), for the
Sign budget `q`, built from an algebraic one-more forger `A`. It samples a
position `ι ∈ [q]` uniformly, the selector whose guess costs the Claim's factor
`q` and needs the budget as an argument (decision A11 of the Theorem 5.3 plan,
one reduction per Claim), answers the `ι`-th issued Sign query, refused queries
issuing nothing as in the game, with the challenge embedded in
`U_ι = a·G + b·X` (p. 46, "Fix ι ∈ [q]"), fails if fewer than `ι` pairs are
issued, and solves for the logarithm the equation that the unsupported
forgery's polynomial `φ_i` (Equation 22) gives at `u_ι`. Two adaptations are the
proof phase's. The core issues nonzero nonces (`uniformUnits`) while the paper's
`U_ι` may vanish, so the masks are conditioned or the zero case coupled away,
and the coefficient of the `u_ι` monomial must remain nonzero after the
evaluation of the other variables (module docstring, *Constants and the
extraction obligation*).
Declared with a `sorry` body until the proof PRs build it. The generator fact
is what its logarithm bookkeeping will need.
-/
noncomputable def omufDLReductionU :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      ℕ → AGMOMUFAdversary F G 1 → DiffieHellman.DLogAdversary F G :=
  sorry

/--
The discrete-log reduction of O24 Claim 5.13 (item (ii), an `η` monomial), built
from an algebraic one-more forger `A`: it embeds the challenge in the crs,
`H = a·G + b·X` with `X₀ = x₀·H` (p. 47), answers every query as the protocol
prescribes, and solves the equation that a forgery polynomial `φ_i` with that
monomial gives at `η`. The masks `(a, b)` are drawn conditioned on `H ≠ 0`, as
`redTrace` of the 3-DL reduction draws its η masks through `reductionMaskSample`
(`docs/DESIGN_ALTERNATIVES.md`, *Conditioned η masks*), since `AGM_OMUFGame`
draws `H` through `setup` from the nonzero elements (issue #149) and an
unconditioned pair would make the reduction's crs differ from the game's with
probability `1/p`. No selector, hence no budget argument (decision A11). The
coefficient of the `η` monomial must remain nonzero after the evaluation of the
other variables, which the example of the module docstring (*Constants and the
extraction obligation*) shows is not automatic. Declared with a `sorry` body
until the proof PRs build it. The generator fact is what its logarithm
bookkeeping will need.
-/
noncomputable def omufDLReductionEta :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      AGMOMUFAdversary F G 1 → DiffieHellman.DLogAdversary F G :=
  sorry

/-- The mixture of two discrete-log adversaries: `B₂` with probability `1/(q + 1)` and `B₁`
otherwise, the choice made independently of the challenge. -/
def dlogMix (q : ℕ) (B₁ B₂ : DiffieHellman.DLogAdversary F G) : DiffieHellman.DLogAdversary F G :=
  fun g X => do
    let i ← $ᵗ (Fin (q + 1))
    if i = 0 then B₂ g X else B₁ g X

/-- The advantage of a mixture is the corresponding mixture of the advantages:
`(q + 1)·Adv(mix) = q·Adv(B₁) + Adv(B₂)`. -/
theorem dlogAdv_dlogMix (gen : G) (q : ℕ) (B₁ B₂ : DiffieHellman.DLogAdversary F G) :
    ((q : ℝ≥0∞) + 1) * dlogAdv gen (dlogMix q B₁ B₂) =
      (q : ℝ≥0∞) * dlogAdv gen B₁ + dlogAdv gen B₂ := by
  have h : dlogAdv gen (dlogMix q B₁ B₂) =
      ∑ i : Fin (q + 1), ((q : ℝ≥0∞) + 1)⁻¹ *
        (if i = 0 then dlogAdv gen B₂ else dlogAdv gen B₁) := by
    unfold dlogAdv
    simp only [DiffieHellman.dlogExp, dlogMix, bind_assoc]
    rw [probOutput_bind_bind_swap, probOutput_bind_eq_sum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [probOutput_uniformSample, Fintype.card_fin]
    push_cast
    congr 1
    by_cases hi : i = 0 <;> simp [hi]
  rw [h, Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero, if_true, if_false, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hq : ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top q, ENNReal.one_ne_top⟩)
  calc _ = (((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1)⁻¹) * dlogAdv gen B₂ +
        (q : ℝ≥0∞) * (((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1)⁻¹) * dlogAdv gen B₁ := by ring
    _ = _ := by rw [hq]; ring

/--
The discrete-log reduction of O24 Theorem 5.11 at `n = 1`, for the Sign budget
`q`, built from an algebraic one-more forger `A`: the mixture, `dlogMix`, of the
reductions of the two Claims that extract a discrete logarithm, `omufDLReductionU`
(Claim 5.12, a `u_ι` monomial, for a chosen issuance index `ι ∈ [q]`) running with
probability `q/(q + 1)` and `omufDLReductionEta` (Claim 5.13, an `η` monomial) with
`1/(q + 1)`, so that `(q + 1)·Adv(mixture) = q·Adv(B_U) + Adv(B_η)`
(`dlogAdv_dlogMix`) and the Claims add up to the theorem's `(q + 1)·εdl` term (decision
A11 of the Theorem 5.3 plan). It is built from the two Claim reductions, which are still
declared with `sorry` bodies.
-/
noncomputable def omufDLReduction (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))]
    (q : ℕ) (A : AGMOMUFAdversary F G 1) : DiffieHellman.DLogAdversary F G :=
  dlogMix q (omufDLReductionU gen q A) (omufDLReductionEta gen A)

/--
The 2-DL reduction of O24 Theorem 5.11 at `n = 1`, built from an algebraic one-more
forger `A`: the mixture, `twoDLMix`, of the three embeddings of Claim 5.14, the challenge in
`x₀`, in `xᵣ` and in `x₁` (`omufTwoDLReductionAt` at the slope patterns `(1, 0, 0)`, `(0, 1, 0)`
and `(0, 0, 1)`), each with probability `1/3`, so that `3·Adv(mixture)` is the sum of the three
advantages (`qdlogAdv_twoDLMix`), the factor `3`.
-/
noncomputable def omufTwoDLReduction (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))]
    (A : AGMOMUFAdversary F G 1) : QDLogAdversary 2 F G :=
  twoDLMix (omufTwoDLReductionAt gen A (1, 0, 0)) (omufTwoDLReductionAt gen A (0, 1, 0))
    (omufTwoDLReductionAt gen A (0, 0, 1))

/-! Uniform-sampling instances for the algebraic one-more oracle spec, needed to push
`simulateQ` through it. They belong beside `AGMOMUFOracleSpec` in `Game.lean`; kept here
for now. -/

noncomputable instance {n : ℕ} : (AGMOMUFOracleSpec F G n).Fintype where
  fintype_B := fun t => by
    cases t
    · exact (inferInstance : Fintype (Option (G × G)))
    · exact (inferInstance : Fintype Bool)

noncomputable instance {n : ℕ} : (AGMOMUFOracleSpec F G n).Inhabited where
  inhabited_B := fun t => by
    cases t
    · exact (inferInstance : Inhabited (Option (G × G)))
    · exact (inferInstance : Inhabited Bool)

noncomputable instance {n : ℕ} : IsUniformSpec (AGMOMUFOracleSpec F G n) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Query translation of the OMUF `n → 1` collapse: coin queries pass through,
`sign` and `verify` are collapsed along `r`. Stateless. -/
noncomputable def omufCollapseImpl {n : ℕ} (r : Fin n → F) :
    QueryImpl (unifSpec + AGMOMUFOracleSpec F G n)
      (OracleComp (unifSpec + AGMOMUFOracleSpec F G 1))
  | .inl t => query (spec := unifSpec + AGMOMUFOracleSpec F G 1) (.inl t)
  | .inr (.sign C ρ) =>
      query (spec := unifSpec + AGMOMUFOracleSpec F G 1)
        (.inr (.sign C (KVAC.Schemes.MicroCMZ.AGMRepr.collapseRepr r ρ)))
  | .inr (.verify m σ ρU ρV) =>
      query (spec := unifSpec + AGMOMUFOracleSpec F G 1)
        (.inr (.verify (collapseMsg r m) σ
          (AGMRepr.collapseRepr r ρU) (AGMRepr.collapseRepr r ρV)))

/-- The `n → 1` collapse of a forgery along `r`. -/
def AGMOMUFForgery.collapse {n : ℕ} (r : Fin n → F) (e : AGMOMUFForgery F G n) :
    AGMOMUFForgery F G 1 :=
  { msg := collapseMsg r e.msg, token := e.token
    reprU := AGMRepr.collapseRepr r e.reprU, reprV := AGMRepr.collapseRepr r e.reprV }

/--
The attribute-lifting transformation of the general `n` proof of O24 Theorem
5.11 (p. 46, "techniques similar to the ones of the previous section", the
Lemma 5.5 embedding): from an `n`-attribute algebraic one-more forger it builds
a single-attribute one against which the `n = 1` reductions run. It samples
scalars `r ∈ Fⁿ` through the private coin oracle, hands the `n`-attribute forger the
public parameters `Xᵢ = rᵢ • X₁`, answers its queries through `omufCollapseImpl` and
collapses its forgeries along `r`. Whether this is the MAC track's Lemma 5.5 embedding
is question C2 of the Theorem 5.3 plan. The construction preserves the Sign budget,
forwarding each Sign query of the `n`-attribute forger exactly once and making none of its
own (`omufToN1_isQueryBoundP`), since `agm_omuf_le` runs the `n = 1` reductions at the same
`q`. Carrying a distinct-combination win into a single-attribute win is
`omufWins_collapse`, and the coupling of the two runs is `collapse_run`.
-/
noncomputable def omufToN1 :
    ∀ {n : ℕ} (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      AGMOMUFAdversary F G n → AGMOMUFAdversary F G 1 :=
  fun {n} _gen _ A =>
    { run := fun H pp => do
        let r ← liftM ($ᵗ (Fin n → F))
        let pp_n : Params G n := (pp.1, pp.2.1, fun i => r i • pp.2.2 0)
        let fs ← simulateQ (omufCollapseImpl r) (A.run H pp_n)
        pure (fs.map (AGMOMUFForgery.collapse r)) }



/-- `omufToN1` preserves the Sign-query bound: coin queries and the sampling of `r` are
Sign-free, and each Sign query is translated to exactly one Sign query. -/
lemma omufToN1_isQueryBoundP {n : ℕ} (gen : G)
    [Fact (Function.Bijective (fun x : F => x • gen))]
    (A : AGMOMUFAdversary F G n) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G n),
      IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    ∀ (H : G) (pp : Params G 1),
      IsQueryBoundP ((omufToN1 gen A).run H pp) AGMOMUFQuery.isSign q := by
  intro H pp
  rw [omufToN1]
  simp only [Fin.isValue, bind_pure_comp]
  rw [← zero_add q]
  apply OracleComp.isQueryBoundP_bind
  · rw [← OracleComp.liftComp_eq_liftM]
    rw [OracleComp.liftComp_def]
    apply OracleComp.IsQueryBoundP.simulateQ_of_step (p := fun _ => False)
    · apply OracleComp.isQueryBoundP_false
    · simp only [IsEmpty.forall_iff, implies_true]
    simp only [not_false_eq_true, forall_const]
    intro t
    exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (fun h => h.elim)
  · intro x h
    rw [OracleComp.isQueryBoundP_map_iff]
    refine OracleComp.IsQueryBoundP.simulateQ_of_step (hq H _) ?_ ?_
    · rintro (t | (⟨C, ρ⟩ | ⟨m, σ, ρU, ρV⟩)) h
      · exact h.elim
      · exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (fun _ => Nat.one_pos)
      · exact h.elim
    · rintro (t | (⟨C, ρ⟩ | ⟨m, σ, ρU, ρV⟩)) h
      · exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (fun h => h.elim)
      · exact absurd trivial h
      · exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (fun h => h.elim)


lemma omufWins_collapse {n : ℕ} (r : Fin n → F) (x₀ xᵣ x₁ : F) (q : ℕ)
    (out : List (AGMOMUFForgery F G n))
    (hlen : out.length = q + 1)
    (hdistinct : (out.map fun e => collapseMsg r e.msg).Nodup)
    (hver : ∀ e ∈ out, verify (x₀, xᵣ, fun i => r i * x₁) e.msg e.token = true) :
    (out.map (AGMOMUFForgery.collapse r)).length = q + 1 ∧
      ((out.map (AGMOMUFForgery.collapse r)).map fun e => e.msg).Nodup ∧
      ∀ e ∈ out.map (AGMOMUFForgery.collapse r),
        verify (x₀, xᵣ, fun _ : Fin 1 => x₁) e.msg e.token = true := by
  constructor
  · rw [List.length_map]
    exact hlen
  constructor
  · rw [List.map_map]
    exact hdistinct
  intro e h
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 h
  obtain hver := hver e' he'
  simp only [AGMOMUFForgery.collapse]
  rw [<- verify_collapse]
  exact hver


/-- Two distinct forgeries whose messages collapse to the same scalar along `r`. -/
def CollapseCollision {n : ℕ} (r : Fin n → F) (out : List (AGMOMUFForgery F G n)) : Prop :=
  ∃ e ∈ out, ∃ e' ∈ out, e.msg ≠ e'.msg ∧ collapseMsg r e.msg = collapseMsg r e'.msg


omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
lemma collapse_nodup_or_collision {n : ℕ} (r : Fin n → F) (out : List (AGMOMUFForgery F G n))
    (hnodup : (out.map fun e => e.msg).Nodup) :
    (out.map fun e => collapseMsg r e.msg).Nodup ∨ CollapseCollision r out := by
    by_contra h
    push Not at h
    obtain ⟨hnot, hno⟩ := h
    apply hnot
    rw [CollapseCollision] at hno
    push Not at hno
    apply List.Nodup.map_on
    · intro x x_in y y_in msg_eq
      specialize hno x x_in y y_in
      rw [not_imp_not] at hno
      obtain xmsg_eq := hno msg_eq
      have msg_inj := List.inj_on_of_nodup_map hnodup
      exact msg_inj x_in y_in xmsg_eq
    exact hnodup.of_map

/-- The log of the collapsed game: representations collapsed, the rest unchanged. -/
def collapseLog {n : ℕ} (r : Fin n → F) (log : AGMOMUFLog F G n) : AGMOMUFLog F G 1 :=
  log.map fun e => (e.1, AGMRepr.collapseRepr r e.2.1, e.2.2)

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
lemma tags_collapseLog {n : ℕ} (r : Fin n → F) (log : AGMOMUFLog F G n) :
    AGMOMUFLog.tags (collapseLog r log) = AGMOMUFLog.tags log := by
    simp only [collapseLog,  AGMOMUFLog.tags]
    rw [List.filterMap_map]
    congr 1


lemma map_if {a b : Type} {m : Type -> Type} (f : a -> b) (p : Prop) (c c' : m a )
     [Decidable p] [Functor m]:
    (f <$> (if p then c else c')) = (if p then f <$> c else f <$> c') := by
    exact apply_ite (Functor.map f) p c c'

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
lemma collapseLog_append {n : ℕ} (r : Fin n → F) (l₁ l₂ : AGMOMUFLog F G n) :
    collapseLog r (l₁ ++ l₂) = collapseLog r l₁ ++ collapseLog r l₂ := by
  simp only [collapseLog, List.map_append]


lemma reprMatches_collapseRepr {n : ℕ} (r : Fin n → F) (ρ : AGMRepr F n) (g₀ H X₀ Xᵣ X₁ : G)
    (tags : List (G × G)) (y : G) :
    reprMatches (AGMRepr.collapseRepr r ρ) g₀ H X₀ Xᵣ (fun _ => X₁) tags y
      ↔ reprMatches ρ g₀ H X₀ Xᵣ (fun i => r i • X₁) tags y := by
  simp only [reprMatches, AGMRepr.eval_collapseRepr]
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
lemma simulateQ_omufCollapseImpl_sign {n : ℕ} {m : Type → Type} [Monad m] [LawfulMonad m]
    (r : Fin n → F) (impl : QueryImpl (unifSpec + AGMOMUFOracleSpec F G 1) m)
    (C : G) (ρ : AGMRepr F n) :
    simulateQ impl (omufCollapseImpl r (.inr (.sign C ρ)))
      = impl (.inr (.sign C (AGMRepr.collapseRepr r ρ))) := by
  simp only [omufCollapseImpl]
  exact simulateQ_spec_query _ _


omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
lemma simulateQ_omufCollapseImpl_verify {n : ℕ} {m : Type → Type} [Monad m] [LawfulMonad m]
    (r : Fin n → F) (impl : QueryImpl (unifSpec + AGMOMUFOracleSpec F G 1) m)
    (msg : Fin n → F) (σ : Code G) (ρU ρV : AGMRepr F n) :
    simulateQ impl (omufCollapseImpl r (.inr (.verify msg σ ρU ρV)))
      = impl (.inr (.verify (collapseMsg r msg) σ (AGMRepr.collapseRepr r ρU)
          (AGMRepr.collapseRepr r ρV))) := by
  simp only [omufCollapseImpl]
  exact simulateQ_spec_query _ _


lemma collapse_step_sign {n : ℕ} (gen : G) (secParam : ℕ)
    (r : Fin n → F) (x₀ xᵣ x₁ : F) (H X₀ Xᵣ X₁ : G)
    (log : AGMOMUFLog F G n) (C : G) (ρ : AGMRepr F n) :
    (simulateQ (agmOMUFImpl gen secParam (x₀, xᵣ, fun _ : Fin 1 => x₁) H (X₀, Xᵣ, fun _ => X₁))
        (omufCollapseImpl r (.inr (.sign C ρ)))).run (collapseLog r log)
      = Prod.map id (collapseLog r) <$>
        (agmOMUFOracleImpl gen secParam (x₀, xᵣ, fun i => r i * x₁) H
          (X₀, Xᵣ, fun i => r i • X₁) (.sign C ρ)).run log := by
  rw [simulateQ_omufCollapseImpl_sign]
  simp only [agmOMUFImpl]
  rw [QueryImpl.add_apply_inr]
  simp only [agmOMUFOracleImpl]
  simp only [StateT.run, StateT.mk]
  rw [map_if]
  simp only [map_bind, map_pure]
  simp only [tags_collapseLog]
  simp only [reprMatches_collapseRepr]
  split_ifs
  · simp only [Prod.map_apply, id, μCMZATCoreSyntax, atIssueSrv]
    simp only [add_apply_inr, smul_add, bind_pure_comp, Functor.map_map]
    simp only [collapseLog_append]
    rfl
  · simp only [Prod.map_apply, id, collapseLog_append]
    rfl

lemma collapse_step_verify {n : ℕ} (gen : G) (secParam : ℕ)
    (r : Fin n → F) (x₀ xᵣ x₁ : F) (H X₀ Xᵣ X₁ : G)
    (log : AGMOMUFLog F G n) (m : Fin n → F) (σ : Code G) (ρU ρV : AGMRepr F n) :
    (simulateQ (agmOMUFImpl gen secParam (x₀, xᵣ, fun _ : Fin 1 => x₁) H (X₀, Xᵣ, fun _ => X₁))
        (omufCollapseImpl r (.inr (.verify m σ ρU ρV)))).run (collapseLog r log)
      = Prod.map id (collapseLog r) <$>
        (agmOMUFOracleImpl gen secParam (x₀, xᵣ, fun i => r i * x₁) H
          (X₀, Xᵣ, fun i => r i • X₁) (.verify m σ ρU ρV)).run log := by
  simp only [omufCollapseImpl]
  erw [simulateQ_spec_query]
  simp only [agmOMUFImpl]
  rw [QueryImpl.add_apply_inr]
  simp only [agmOMUFOracleImpl]
  simp only [StateT.run, StateT.mk]
  simp only [map_pure]
  simp only [reprMatches_collapseRepr]
  simp only [Prod.map_apply, id, tags_collapseLog, μCMZATCoreSyntax, atIssueSrv, verify_collapse]
  rfl


lemma collapse_step_coin {n : ℕ} (gen : G) (secParam : ℕ)
    (r : Fin n → F) (x₀ xᵣ x₁ : F) (H X₀ Xᵣ X₁ : G)
    (log : AGMOMUFLog F G n) (t : ℕ) :
    (simulateQ (agmOMUFImpl gen secParam (x₀, xᵣ, fun _ : Fin 1 => x₁) H (X₀, Xᵣ, fun _ => X₁))
        (omufCollapseImpl r (.inl t))).run (collapseLog r log)
      = Prod.map id (collapseLog r) <$>
        (agmOMUFImpl gen secParam (x₀, xᵣ, fun i => r i * x₁) H
          (X₀, Xᵣ, fun i => r i • X₁) (.inl t)).run log := by
  simp only [omufCollapseImpl]
  erw [simulateQ_spec_query]
  simp only [agmOMUFImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
  simp [liftM, monadLift, MonadLift.monadLift, Functor.map_map]


lemma collapse_run {n : ℕ} {α : Type} (gen : G) (secParam : ℕ)
    (r : Fin n → F) (x₀ xᵣ x₁ : F) (H X₀ Xᵣ X₁ : G)
    (oa : OracleComp (unifSpec + AGMOMUFOracleSpec F G n) α) (log : AGMOMUFLog F G n) :
    (simulateQ (agmOMUFImpl gen secParam (x₀, xᵣ, fun _ : Fin 1 => x₁) H (X₀, Xᵣ, fun _ => X₁))
        (simulateQ (omufCollapseImpl r) oa)).run (collapseLog r log)
      = Prod.map id (collapseLog r) <$>
        (simulateQ (agmOMUFImpl gen secParam (x₀, xᵣ, fun i => r i * x₁) H
          (X₀, Xᵣ, fun i => r i • X₁)) oa).run log := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id]
  | query_bind t oa ih => simp only [simulateQ_bind, simulateQ_query]
                          simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
                            StateT.run_bind, map_bind]
                          rcases t with t | (⟨C, ρ⟩ | ⟨m, σ, ρU, ρV⟩)
                          · rw [collapse_step_coin]
                            rw [bind_map_left]
                            exact bind_congr fun a => ih _ _
                          · rw [collapse_step_sign]
                            simp only [OracleSpec.Range, OracleSpec.add_apply_inr]
                            rw [bind_map_left]
                            rw [agmOMUFImpl_inr]
                            exact bind_congr fun a => ih _ _
                          · rw [collapse_step_verify]
                            simp only [OracleSpec.Range, OracleSpec.add_apply_inr]
                            rw [bind_map_left]
                            exact bind_congr fun a => ih _ _





/-! ## The statements -/

variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/-! ## The Claims

The three Claims of the `n = 1` proof, over the case events of `CaseEvents.lean`
read off the trace of `Transcript.lean`: each bounds the trace probability
`Pr[ event | agmOMUFTrace gen secParam A ]` of one item of the case split by the
paper's constant and the advantage of that item's reduction. Only Claim 5.12
carries the budget hypothesis, since its constant `q` is the selector's range,
the budget rather than the actual number of issued pairs, which the reduction
cannot know before running the forger. Claims 5.13 and 5.14 embed the challenge
in the crs or the public parameters and hold for every forger. The theorem
invokes the three under its hypothesis and they add up to Equation 23 (module
docstring). The docstrings state the paper's arguments, which the extraction
obligation of the module docstring qualifies. Claims 5.12 and 5.13 are stated first and
`sorry`d. Claim 5.14 is proved (`TwoDLExtraction.lean`), with the degenerate probability of its
extraction as an explicit term. -/

/--
**O24 Claim 5.12**, item (i), the adversary wins and some forgery polynomial has
a nonzero monomial in some `u_j`, with probability at most
`q·(1/p + Adv^dl) + εdegU` for the reduction `omufDLReductionU gen q A`, with `εdegU` the
degenerate probability `omufDegenerateProbU`. The paper's
`1/p` is the degenerate mask under the substitution `u_ι ↦ a + b·χ`, `b`
uniform and hidden by `a` (p. 46), the factor `q` the selector's guess. That the
coefficient of the monomial remains nonzero after the evaluation of the other
variables at the run's values is the extraction obligation of the module
docstring, which the term `εdegU` accounts for: the paper takes it to be `0`. Printed
constant, provisional (module docstring, *Constants and the extraction
obligation*).
-/
theorem omuf_claim_5_12 (A : AGMOMUFAdversary F G 1) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G 1), IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    Pr[ OMUFTrace.CaseU gen secParam | agmOMUFTrace gen secParam A ] ≤
      (q : ℝ≥0∞) *
        ((Fintype.card F : ℝ≥0∞)⁻¹ + dlogAdv gen (omufDLReductionU gen q A)) +
      omufDegenerateProbU gen secParam A := by
  sorry

/--
**O24 Claim 5.13**, item (ii), the adversary wins and some forgery polynomial
has a nonzero monomial in `η`, with probability at most `1/p + Adv^dl + εdegη` for the
reduction `omufDLReductionEta gen A`, with `εdegη` the degenerate probability
`omufDegenerateProbEta`. No factor `q`, since the reduction embeds
the challenge in the crs and no position is chosen, so no budget hypothesis. The
module
docstring's example, a forger that learns `x₀ + xᵣ` through Verify queries,
realises the event with nothing for this reduction to extract, which is why the statement
carries `εdegη`. Printed constant,
provisional (module docstring, *Constants and the extraction obligation*).
-/
theorem omuf_claim_5_13 (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseEta gen secParam | agmOMUFTrace gen secParam A ] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + dlogAdv gen (omufDLReductionEta gen A) +
        omufDegenerateProbEta gen secParam A := by
  sorry

/--
**O24 Claim 5.14**, item (iii), the adversary wins and some forgery polynomial
has a nonzero monomial in `x₀`, `xᵣ` or `x₁`, with probability at most
`3·(1/p + Adv^2-dl)` for the reduction `omufTwoDLReduction gen A`, the same
2-DL reduction the theorem cites, its factor `3` the three near-identical
embeddings (p. 47, the `x₀` case written out, `X₀ = a·H + b·η·X`, the `xᵣ` and
`x₁` cases "almost identical"). No budget hypothesis, the reduction embeds the
challenge in the public parameters. Its crs `H` is drawn from the nonzero
elements as `AGM_OMUFGame` does, so that the two games agree on the crs
(*Conditioned η masks*, `docs/DESIGN_ALTERNATIVES.md`). The extraction
obligation of the module docstring applies: the bound carries the degenerate probability
`omufDegenerateProb` of the extraction as an extra term, which the paper's argument takes to be
`0`. Printed constant, provisional (module docstring, *Constants and the extraction obligation*).
-/
theorem omuf_claim_5_14 (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseX gen secParam | agmOMUFTrace gen secParam A ] ≤
      3 * ((Fintype.card F : ℝ≥0∞)⁻¹ + twoDlogAdv gen (omufTwoDLReduction gen A)) +
        omufDegenerateProb gen secParam A := by
  refine (probEvent_mono fun t ht hx => OMUFTrace.caseX_imp gen secParam t hx).trans ?_
  have h1 := probEvent_or_le (agmOMUFTrace gen secParam A) (OMUFTrace.CaseX0 gen secParam)
    (fun t => t.CaseXr gen secParam ∨ t.CaseX1 gen secParam)
  have h2 := probEvent_or_le (agmOMUFTrace gen secParam A) (OMUFTrace.CaseXr gen secParam)
    (OMUFTrace.CaseX1 gen secParam)
  have hmix := qdlogAdv_twoDLMix gen (omufTwoDLReductionAt gen A (1, 0, 0))
    (omufTwoDLReductionAt gen A (0, 1, 0)) (omufTwoDLReductionAt gen A (0, 0, 1))
  have hsum := add_le_add (omuf_claim_5_14_x0 gen secParam A)
    (add_le_add (omuf_claim_5_14_xr gen secParam A) (omuf_claim_5_14_x1 gen secParam A))
  refine (h1.trans (add_le_add_right h2 _)).trans (hsum.trans (le_of_eq ?_))
  unfold omufDegenerateProb
  have hmix' : 3 * twoDlogAdv gen (omufTwoDLReduction gen A) =
      twoDlogAdv gen (omufTwoDLReductionAt gen A (1, 0, 0)) +
        twoDlogAdv gen (omufTwoDLReductionAt gen A (0, 1, 0)) +
          twoDlogAdv gen (omufTwoDLReductionAt gen A (0, 0, 1)) := hmix
  rw [mul_add, hmix']
  ring

omit hgen in
/-- The AGM advantage is the trace probability of the win. -/
theorem AGM_OMUFAdv_eq_probEvent_wins (A : AGMOMUFAdversary F G 1) :
    AGM_OMUFAdv gen A secParam =
      Pr[ fun t => t.Wins gen secParam | agmOMUFTrace gen secParam A ] := by
  unfold AGM_OMUFAdv
  rw [AGM_OMUFGame_eq_trace, bind_pure_comp, ← probEvent_eq_eq_probOutput, probEvent_map]
  congr 1
  funext t
  exact propext decide_eq_true_iff

/-- The advantage is at most the sum of the probabilities of the three case events: the events
cover a win (`omuf_cover`), and a union bound. -/
theorem AGM_OMUFAdv_le_cases (A : AGMOMUFAdversary F G 1) :
    AGM_OMUFAdv gen A secParam ≤
      Pr[ OMUFTrace.CaseU gen secParam | agmOMUFTrace gen secParam A ] +
        (Pr[ OMUFTrace.CaseEta gen secParam | agmOMUFTrace gen secParam A ] +
          Pr[ OMUFTrace.CaseX gen secParam | agmOMUFTrace gen secParam A ]) := by
  rw [AGM_OMUFAdv_eq_probEvent_wins]
  refine (probEvent_mono fun t ht hw => omuf_cover gen secParam A t ht hw).trans ?_
  have h1 := probEvent_or_le (agmOMUFTrace gen secParam A) (OMUFTrace.CaseU gen secParam)
    (fun t => t.CaseEta gen secParam ∨ t.CaseX gen secParam)
  have h2 := probEvent_or_le (agmOMUFTrace gen secParam A) (OMUFTrace.CaseEta gen secParam)
    (OMUFTrace.CaseX gen secParam)
  exact h1.trans (add_le_add_right h2 _)

/--
**O24 Theorem 5.11 at `n = 1`, Equation 23**, in the shape drawn in the module
docstring. Proved from Claims 5.12 to 5.14, of which 5.12 and 5.13 are stated below and
`sorry`d: the advantage is the trace probability of the win (`AGM_OMUFAdv_eq_probEvent_wins`), a win
presents `q + 1` forgeries against at most `q` issued pairs, so by pigeonhole one forgery
is not the unblinding of any pair and its polynomial `φ_i` has a nonzero monomial in one
of the three variable groups (`omuf_cover`), the union bound adds the three Claims'
probabilities (`AGM_OMUFAdv_le_cases`), and their constants add up to Equation 23 since
the theorem's discrete-log reduction is the mixture of the two Claim reductions
(`dlogAdv_dlogMix`, `omufBoundN1_eq_of_mix`).
-/
theorem agm_omuf_le_n1 (A : AGMOMUFAdversary F G 1) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G 1), IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    AGM_OMUFAdv gen A secParam ≤
      omufBoundN1 F q (dlogAdv gen (omufDLReduction gen q A))
        (twoDlogAdv gen (omufTwoDLReduction gen A)) + omufDegenerateProbAll gen secParam A := by
  refine (AGM_OMUFAdv_le_cases gen secParam A).trans ?_
  have hdef : omufDLReduction gen q A =
      dlogMix q (omufDLReductionU gen q A) (omufDLReductionEta gen A) := rfl
  have hmix := dlogAdv_dlogMix gen q (omufDLReductionU gen q A) (omufDLReductionEta gen A)
  rw [← hdef] at hmix
  have h12 := omuf_claim_5_12 gen secParam A q hq
  have h13 := omuf_claim_5_13 gen secParam A
  have h14 := omuf_claim_5_14 gen secParam A
  have hsum := add_le_add h12 (add_le_add h13 h14)
  have heq := omufBoundN1_eq_of_mix F q _ _ _ (twoDlogAdv gen (omufTwoDLReduction gen A)) hmix
  refine hsum.trans (le_of_eq ?_)
  unfold omufDegenerateProbAll
  rw [← heq]
  ring

/--
**O24 Theorem 5.11, every `n`**, in the shape drawn in the module docstring,
stated first and `sorry`d, with the paper's printed bound. The proof splits the
winning event by whether the forgeries' attribute combinations are pairwise
distinct: the distinct case runs the `n = 1` statement `agm_omuf_le_n1` on the
transformed adversary `omufToN1 gen A`, the colliding case is the gap-DL
reduction, and the two add `2/p + Adv^gapdl` to Equation 23, with the degenerate
probabilities of the transformed adversary as an extra term. The domain `0 < n`
is §3.4's, as for the plain game.
-/
theorem agm_omuf_le {n : ℕ} (hn : 0 < n) (A : AGMOMUFAdversary F G n) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G n), IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    AGM_OMUFAdv gen A secParam ≤
      omufBound F q (dlogAdv gen (omufDLReduction gen q (omufToN1 gen A)))
        (twoDlogAdv gen (omufTwoDLReduction gen (omufToN1 gen A)))
        (gapDlogAdv gen (omufGapDLReduction gen A)) +
      omufDegenerateProbAll gen secParam (omufToN1 gen A) := by
  sorry

end KVAC.Schemes.MicroCMZ
