/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.AGMOneMoreUnforgeability
import KVAC.Preliminaries.Assumptions
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# μCMZ_AT one-more unforgeability, `n = 1` — the Theorem 5.11 target statement (O24 §5.6)

Theorem 5.11 of Orrù, *Revisiting Keyed-Verification Anonymous Credentials*
(IACR ePrint 2024/1552), at `n = 1` (Equation 23), for the μCMZ_AT core in the
AGM-instrumented game of `KVAC.Schemes.MicroCMZ.AGMOneMoreUnforgeability`.
Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of item 17 (issue
#189), first of three PRs; the general `n` statement and the Claims 5.12 to 5.14
with their polynomial layer follow. Stated first and `sorry`d on the pattern of
`AGMReduction/SecurityN1.lean`, so that the reduction reviews against a visible
target; the blueprint node `mucmz_at_agm_omuf_n1` shows "contains sorry" until
the proof lands.

## The statement and its parts

  agm_omuf_le_n1 :   AGM_OMUFAdv gen A secParam  ≤  omufBoundN1 F q εdl ε2dl
    for every  A : AGMOMUFAdversary F G 1  with
      ∀ H pp, IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q    at most q Sign queries,
                                                                   refused ones included
    where
      omufBoundN1 F q εdl ε2dl = (q + 4)/p + (q + 1)·εdl + 3·ε2dl   Equation 23, printed
                                                                   constants, provisional
      εdl  = dlogAdv gen (omufDLReduction gen q A)                 DL reduction, Claims 5.12
                                                                   (u_ι monomial) and 5.13 (η)
      ε2dl = twoDlogAdv gen (omufTwoDLReduction gen A)             2-DL reduction, Claim 5.14
                                                                   (x₀, xᵣ, x₁, three cases)

The two reductions are declared with `sorry` bodies, the first sorried
definitions in the repository, and are built with the proofs of the Claims over
the polynomial layer of Equations 17 to 22.

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
two named reductions. Their `sorry` sits at the whole function type, not under
the binders, so that the placeholders are not definitionally independent of
their arguments (a `def … (A) := sorry` would make `f A₁ = f A₂` hold by `rfl`).
No lemma may be stated about them beyond this theorem until they are built,
since anything provable about an unspecified body holds of every inhabitant. The
discrete-log reduction takes the budget `q`, since a selector over the `q`
issuance positions of Claim 5.12 needs it; the 2-DL reduction selects among
three fixed cases.

## Constants

`omufBoundN1` carries the printed constants of Equation 23, provisional: the
repository already documents one Schwartz–Zippel undercount in this section
family (`3/p` for a printed `1/p`, `AGMPolynomial.lean`), and the Claims share
the pattern. The constant audit of the proof phase settles them, with an errata
item on any change, and the named definition makes such a change one line. The
printed general bound, `(q + 6)/p + …`, exceeds Equation 23 by `2/p + Adv^gapdl`
and will be stated separately with the general `n` extension.

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

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

/-! ## The reductions, named now and built with the proofs

The generator and its bijectivity fact are explicit binders here rather than
section variables, since a `sorry` body mentions neither and a section variable
joins a definition only when mentioned. The `sorry` inhabits the whole function
type (module docstring, *The shape of the statement*). -/

/--
The discrete-log reduction of O24 Theorem 5.11 at `n = 1`, for the Sign budget
`q`, built from an algebraic one-more forger `A`: it embeds the challenge into
the game it simulates for `A` and extracts the logarithm from the polynomial
`φ_i` (Equation 22) of the unsupported forgery, at a `u_ι` monomial for a chosen
issuance index `ι ∈ [q]` (Claim 5.12) or at an `η` monomial (Claim 5.13). The
paper's factor `(q + 1)` is the union of these cases; whether one selector
reduction or one reduction per case carries it is open with the MAC track
(question C1 of the Theorem 5.3 plan), and the budget argument is what a
selector over the `q` positions needs. Declared with a `sorry` body until the
proof PRs build it; the generator fact is what the construction's logarithm
bookkeeping (`glog`) will need.
-/
noncomputable def omufDLReduction :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))],
      ℕ → AGMOMUFAdversary F G 1 → DiffieHellman.DLogAdversary F G :=
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

/-! ## The statement -/

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

end KVAC.Schemes.MicroCMZ
