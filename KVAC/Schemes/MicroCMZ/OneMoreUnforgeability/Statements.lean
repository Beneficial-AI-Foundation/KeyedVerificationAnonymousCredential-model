/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.CaseEvents
import KVAC.Preliminaries.Assumptions
import VCVio.OracleComp.QueryTracking.QueryBound

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
  omuf_claim_5_14 :  Pr[ CaseX   | agmOMUFTrace gen secParam A ]  ≤  3·(1/p + ε2dl)   item (iii)
    for every  A : AGMOMUFAdversary F G 1,  over the case events of CaseEvents.lean,
    the first under the budget hypothesis, the other two without
    where
      εU = dlogAdv gen (omufDLReductionU gen q A)         Claim 5.12, selector over ι ∈ [q]
      εη = dlogAdv gen (omufDLReductionEta gen A)         Claim 5.13, challenge in the crs
    and the theorem's εdl is the mixture  q/(q + 1)·εU + 1/(q + 1)·εη,  so that
      q·(1/p + εU) + (1/p + εη) + 3·(1/p + ε2dl)  =  omufBoundN1 F q εdl ε2dl
    once the win is covered by the three events (pigeonhole, proof phase).

The `n = 1` case is the one the paper proves directly. General `n` follows from
it (p. 46): the winning event splits by whether the forgeries' attribute
combinations `Σᵢ mᵢ·Xᵢ` are pairwise distinct, the distinct case reduces to
`n = 1` on a transformed adversary, and the colliding case to gap-DL by an
argument in the style of Lemma 5.5 (which the paper's text cites as Theorem
5.5). The six named constructions, the theorem's two reductions, the two
per-Claim discrete-log reductions, the attribute-lifting transformation
`omufToN1 : AGMOMUFAdversary F G n → AGMOMUFAdversary F G 1`, and the gap-DL
reduction, are declared with `sorry` bodies, the first sorried definitions in
the repository, and are built with the proofs of the Claims over the polynomial
layer of Equations 17 to 22 (`Polynomial.lean`, `CaseEvents.lean`). Whether the
transformation reuses the Lemma 5.5 embedding of the MAC track is open with
Semar (question C2 of the Theorem 5.3 plan). One constraint is on record: the
adversary shape carries no private coin oracle, so a transformation that needs
randomness must fix its coins in the construction, with a fixed-coins argument
in the proof, or the shape must grow a coin arm (Phase B). Extra Sign queries
are not a source of randomness, they break the budget and the one-more count.

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
the overhead of the general `n` argument, `1/p` from each of its two cases.

The paper's `1/p` in each Claim is the degenerate mask, `b = 0` or the
substituted polynomial in `χ` trivial, `b` uniform and hidden by `a`. A second
event sits between the case events and the extraction. The events are the
paper's items, a nonzero monomial in the variable of a formal polynomial, while
the reduction extracts from the univariate polynomial left after evaluating
every other variable at the run's values, and the monomial's coefficient, a
nonzero polynomial in those other variables, can vanish there. An example: with
no Sign query and Verify queries `(0, (G, c·G))` over all `c`, a forger learns
`k = x₀ + xᵣ` and outputs the forgery `(0, (H, k·H))` represented over `H`,
which wins whenever `H ≠ 0`. Its polynomial `η·(x₀ + xᵣ − k)` has an `η`
monomial, so `CaseEta` holds with probability `1 − 1/p`, yet at the run's key
nothing in `η` remains for the Claim 5.13 reduction, while the `x₀` embedding
of Claim 5.14 extracts from it. Schwartz–Zippel bounds such a collapse by `d/p`
only for a polynomial independent of the run's values, and honest Verify
answers break that independence, each being a test of the key, with no Verify
budget in the game. Whether the Claims keep the paper's events, with a covering
argument that routes every winning polynomial to a reduction that extracts from
it, or move to evaluated events, and whether a Verify budget and a
per-Verify-query term join the statements, is an obligation of the proof phase
beyond the constant audit, and a decision of the Theorem 5.3 plan. The paper's
own item list (p. 45) cites the three Claims as Theorems 5.12 to 5.14.

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

/--
The printed bound of O24 Theorem 5.11 for every `n`,
`(q + 6)/p + (q + 1)·εdl + 3·ε2dl + εgap`, with `εgap` the gap-DL advantage of
the collision-case reduction. Exceeds `omufBoundN1` by `2/p + εgap`, `1/p` from
each case of the general `n` argument. Printed constants, provisional (module
docstring, *Constants*).
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
The discrete-log reduction of O24 Theorem 5.11 at `n = 1`, for the Sign budget
`q`, built from an algebraic one-more forger `A`: it embeds the challenge into
the game it simulates for `A` and extracts the logarithm from the polynomial
`φ_i` (Equation 22) of the unsupported forgery, at a `u_ι` monomial for a chosen
issuance index `ι ∈ [q]` (Claim 5.12) or at an `η` monomial (Claim 5.13). The
paper's factor `(q + 1)` is the union of these cases. Each Claim has its own
reduction below, `omufDLReductionU` and `omufDLReductionEta` (decision A11 of
the Theorem 5.3 plan), and this one is defined in the proof phase as their
mixture, running the first with probability `q/(q + 1)` and the second with
`1/(q + 1)`, so that `(q + 1)·Adv(mixture) = q·Adv(B_U) + Adv(B_η)` and the
Claims add up to the theorem's `(q + 1)·εdl` term. The budget argument is the
selector's. Declared with a `sorry` body until the proof PRs build it; the
generator fact is what the construction's logarithm bookkeeping (`glog`) will
need.
-/
noncomputable def omufDLReduction :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      ℕ → AGMOMUFAdversary F G 1 → DiffieHellman.DLogAdversary F G :=
  sorry

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
and the coefficient of the `u_ι` monomial must survive the evaluation of the
other variables (module docstring, *Constants and the extraction obligation*).
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
prescribes, and solves the equation that the unsupported forgery's polynomial
`φ_i` gives at `η`. No selector, hence no budget argument (decision A11). The
coefficient of the `η` monomial must survive the evaluation of the other
variables, which the example of the module docstring (*Constants and the
extraction obligation*) shows is not automatic. Declared with a `sorry` body
until the proof PRs build it. The generator fact is what its logarithm
bookkeeping will need.
-/
noncomputable def omufDLReductionEta :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      AGMOMUFAdversary F G 1 → DiffieHellman.DLogAdversary F G :=
  sorry

/--
The 2-DL reduction of O24 Theorem 5.11 at `n = 1`, built from an algebraic
one-more forger `A`: it extracts from an `x₀`, `xᵣ` or `x₁` monomial of the
unsupported forgery's polynomial `φ_i` (Claim 5.14, three near-identical cases,
the factor `3`). Declared with a `sorry` body until the proof PRs build it.
-/
noncomputable def omufTwoDLReduction :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      AGMOMUFAdversary F G 1 → QDLogAdversary 2 F G :=
  sorry

/--
The attribute-lifting transformation of the general `n` proof of O24 Theorem
5.11 (p. 46, "techniques similar to the ones of the previous section", the
Lemma 5.5 embedding): from an `n`-attribute algebraic one-more forger it builds
a single-attribute one against which the `n = 1` reductions run. Declared with
a `sorry` body until built; whether it reuses the MAC track's Lemma 5.5
embedding is question C2 of the Theorem 5.3 plan. Two constraints on the
construction: it must preserve the Sign budget, forwarding each Sign query of
the `n`-attribute forger exactly once and making none of its own, since
`agm_omuf_le` runs the `n = 1` reductions at the same `q`, while translating
the representation gates and the transcript and carrying a distinct-combination
win into a single-attribute win; and the adversary shape has no private coin
oracle (module docstring), so its coins are fixed in the construction or the
shape grows a coin arm.
-/
noncomputable def omufToN1 :
    ∀ {n : ℕ} (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      AGMOMUFAdversary F G n → AGMOMUFAdversary F G 1 :=
  sorry

/--
The gap-DL reduction of the collision case of O24 Theorem 5.11 at general `n`
(p. 46, two forgeries with equal attribute combination `Σᵢ mᵢ·Xᵢ`, "reduced to
DL using an argument similar to Theorem 5.5", the paper's text citing its
Lemma 5.5 as a theorem), built from an `n`-attribute algebraic one-more
forger. Unlike the transformation, it may randomise freely, since
`GapDLogAdversary` carries a uniform-sampling arm. Declared with a `sorry` body
until built.
-/
noncomputable def omufGapDLReduction :
    ∀ {n : ℕ} (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      AGMOMUFAdversary F G n → GapDLogAdversary F G :=
  sorry

/-! ## The statements -/

variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/--
**O24 Theorem 5.11 at `n = 1`, Equation 23**, in the shape drawn in the module
docstring, stated first and `sorry`d. The proof runs at the actual number `r` of
Sign queries, `r ≤ q` by the hypothesis: a win presents `r + 1` forgeries
against at most `r` issued pairs, so by pigeonhole one forgery is not the
unblinding of any pair, its polynomial `φ_i` has a nonzero monomial in one of
the three variable groups, and Claims 5.12 to 5.14 bound each case over the
polynomial layer of Equations 17 to 22, `r ≤ q` giving the stated constants.
-/
theorem agm_omuf_le_n1 (A : AGMOMUFAdversary F G 1) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G 1), IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    AGM_OMUFAdv gen A secParam ≤
      omufBoundN1 F q (dlogAdv gen (omufDLReduction gen q A))
        (twoDlogAdv gen (omufTwoDLReduction gen A)) := by
  sorry

/--
**O24 Theorem 5.11, every `n`**, in the shape drawn in the module docstring,
stated first and `sorry`d, with the paper's printed bound. The proof splits the
winning event by whether the forgeries' attribute combinations are pairwise
distinct: the distinct case runs the `n = 1` statement `agm_omuf_le_n1` on the
transformed adversary `omufToN1 gen A`, the colliding case is the gap-DL
reduction, and the two add `2/p + Adv^gapdl` to Equation 23. The domain `0 < n`
is §3.4's, as for the plain game.
-/
theorem agm_omuf_le {n : ℕ} (hn : 0 < n) (A : AGMOMUFAdversary F G n) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G n), IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    AGM_OMUFAdv gen A secParam ≤
      omufBound F q (dlogAdv gen (omufDLReduction gen q (omufToN1 gen A)))
        (twoDlogAdv gen (omufTwoDLReduction gen (omufToN1 gen A)))
        (gapDlogAdv gen (omufGapDLReduction gen A)) := by
  sorry

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
obligation of the module docstring qualifies. Stated first and `sorry`d. -/

/--
**O24 Claim 5.12**, item (i), the adversary wins and some forgery polynomial has
a nonzero monomial in some `u_j`, with probability at most
`q·(1/p + Adv^dl)` for the reduction `omufDLReductionU gen q A`. The paper's
`1/p` is the degenerate mask under the substitution `u_ι ↦ a + b·χ`, `b`
uniform and hidden by `a` (p. 46), the factor `q` the selector's guess. That the
coefficient of the monomial survives the evaluation of the other variables at
the run's values is the extraction obligation of the module docstring. Printed
constant, provisional (module docstring, *Constants and the extraction
obligation*).
-/
theorem omuf_claim_5_12 (A : AGMOMUFAdversary F G 1) (q : ℕ)
    (hq : ∀ (H : G) (pp : Params G 1), IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q) :
    Pr[ OMUFTrace.CaseU gen secParam | agmOMUFTrace gen secParam A ] ≤
      (q : ℝ≥0∞) *
        ((Fintype.card F : ℝ≥0∞)⁻¹ + dlogAdv gen (omufDLReductionU gen q A)) := by
  sorry

/--
**O24 Claim 5.13**, item (ii), the adversary wins and some forgery polynomial
has a nonzero monomial in `η`, with probability at most `1/p + Adv^dl` for the
reduction `omufDLReductionEta gen A`. No factor `q`, since the challenge sits in
the crs and no position is chosen, so no budget hypothesis. The module
docstring's example, a forger that learns `x₀ + xᵣ` through Verify queries,
realises the event with nothing for this reduction to extract, so the statement
rests on the extraction obligation recorded there. Printed constant,
provisional (module docstring, *Constants and the extraction obligation*).
-/
theorem omuf_claim_5_13 (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseEta gen secParam | agmOMUFTrace gen secParam A ] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + dlogAdv gen (omufDLReductionEta gen A) := by
  sorry

/--
**O24 Claim 5.14**, item (iii), the adversary wins and some forgery polynomial
has a nonzero monomial in `x₀`, `xᵣ` or `x₁`, with probability at most
`3·(1/p + Adv^2-dl)` for the reduction `omufTwoDLReduction gen A`, the same
2-DL reduction the theorem cites, its factor `3` the three near-identical
embeddings (p. 47, the `x₀` case written out, `X₀ = a·H + b·η·X`, the `xᵣ` and
`x₁` cases "almost identical"). No budget hypothesis, the challenge sits in
the public parameters. The extraction obligation of the module docstring
applies. Printed constant, provisional (module docstring, *Constants and the
extraction obligation*).
-/
theorem omuf_claim_5_14 (A : AGMOMUFAdversary F G 1) :
    Pr[ OMUFTrace.CaseX gen secParam | agmOMUFTrace gen secParam A ] ≤
      3 * ((Fintype.card F : ℝ≥0∞)⁻¹ + twoDlogAdv gen (omufTwoDLReduction gen A)) := by
  sorry

end KVAC.Schemes.MicroCMZ
