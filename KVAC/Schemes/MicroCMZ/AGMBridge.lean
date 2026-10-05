/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.AlgebraicMAC.Security
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import KVAC.Schemes.MicroCMZ.SimulateQGuarded

/-!
# Well-behaved algebraic adversaries and their translation to the plain game

`AGM_UF_CMVAGame` (`KVAC.Schemes.MicroCMZ.AlgebraicMAC`) is the *instrumented* unforgeability
game: its oracles demand algebraic representations and gate their answers on transcript
consistency, and its win condition carries an extra consistency conjunct. The paper's Theorem 5.1
(O24) is a statement about the *plain* Figure 5 game — `UF_CMVAGame` of
`KVAC.Core.AlgebraicMAC.Security` — restricted to algebraic adversaries. This file supplies the
vocabulary connecting the two:

- `agmGood` — per-query goodness for the instrumented oracles: `sign` is always good, `verify` is
  good iff the submitted representations are transcript-consistent (exactly the condition
  `agmOracleImpl` gates on), and `help` is never good (the paper-faithful Figure 5 game has no
  Help oracle, so a bridgeable adversary must never query it).
- `WellBehaved` — the runtime predicate on an `AGMUFAdversary` making it a genuine *algebraic
  adversary for the plain game*: against every honest oracle configuration, (1) the
  `agmGood`-guarded run never fails — no reachable inconsistent representation, no reachable
  `help` query (`guardImpl` aborts on the first bad query, so `Pr[⊥ | ·] = 0` certifies both) —
  and (2) every reachable forgery output is consistent over the final transcript.
- `AGMUFAdversary.toUFAdversary` — the forgetful translation `AGMUFAdversary F G n →
  UFAdversary (μCMZBaseMACSyntax F gen)`: forward `sign`/`verify` queries with the
  representations dropped, answer `help` queries locally by `false` (`WellBehaved` rules them out
  in the AGM game), and drop the forgery representations from the output. At attribute counts
  other than `n` the translated adversary outputs a junk forgery.

Quantifying `WellBehaved` over *all* `(sk, H, pp)` — not just those reachable from
`setup`/`keygen` — is a harmless strengthening: a genuinely algebraic adversary computes its
representations from the group elements it received, irrespective of how they were sampled.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core OracleSpec OracleComp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}
variable (gen : G)

/-! ## Per-query goodness and the guarded oracle -/

/-- Goodness of one instrumented query against the current transcript: `sign` is always good,
`verify` is good iff the submitted tag representations are transcript-consistent (the exact
condition the `verify` arm of `agmOracleImpl` gates on), and `help` is never good (the plain
Figure 5 game has no Help oracle). -/
def agmGood (H : G) (pp : Params G n) : AGMQuery F G n → AGMLog F G n → Prop
  | .sign _, _ => True
  | .verify _ σ ρU ρV, log =>
      ρU.eval gen H pp.1 pp.2.1 pp.2.2 (log.map Prod.snd) = σ.1 ∧
      ρV.eval gen H pp.1 pp.2.1 pp.2.2 (log.map Prod.snd) = σ.2
  | .help _ _ _ _ _ _, _ => False

instance instDecidableAgmGood (H : G) (pp : Params G n) (t : AGMQuery F G n) (log : AGMLog F G n) :
    Decidable (agmGood gen H pp t log) := by
  cases t <;> simp only [agmGood] <;> infer_instance

/-- The honest instrumented oracle guarded by `agmGood`: behaves like `agmOracleImpl` while
every query is `agmGood`, and aborts on the first bad one. The guard is stricter than the
oracle's own gates: `agmOracleImpl` answers a consistent `help` query, `agmGood` rejects every
`help` query. -/
noncomputable abbrev guardedAgmOracleImpl (secParam : ℕ) (sk : Key F n) (H : G)
    (pp : Params G n) :
    QueryImpl (AGMOracleSpec F G n) (StateT (AGMLog F G n) (OptionT ProbComp)) :=
  guardImpl (agmOracleImpl (gen := gen) secParam sk H pp) (agmGood gen H pp)

/-! ## Well-behaved algebraic adversaries -/

/-- Consistency of a forgery output over its final transcript: the representations `ρU`/`ρV`
evaluate to the submitted tag halves against the basis extended by all issued tags. Same shape as
the `consistent` conjunct of `AGM_UF_CMVAGame`'s win condition. -/
def ForgeryConsistent (H : G) (pp : Params G n)
    (z : ((Fin n → F) × (G × G) × AGMRepr F n × AGMRepr F n) × AGMLog F G n) : Prop :=
  match z with
  | ((_, σStar, ρU, ρV), log) =>
      ρU.eval gen H pp.1 pp.2.1 pp.2.2 (log.map Prod.snd) = σStar.1 ∧
      ρV.eval gen H pp.1 pp.2.1 pp.2.2 (log.map Prod.snd) = σStar.2

/-- A *well-behaved* algebraic adversary: against every honest oracle configuration
`(sk, H, pp)`,

1. the `agmGood`-guarded run never fails — equivalently, no execution path reaches an
   inconsistent `verify` representation or a `help` query (the guard aborts on the first bad
   query, so zero failure probability certifies unreachability); and
2. every reachable forgery output is consistent over the final transcript.

This is the formal content of "the adversary is algebraic *and plays the plain game*": its
representations are always truthful, and it never uses the Help oracle absent from Figure 5. The
gates of `agmOracleImpl` and the consistency conjunct of `AGM_UF_CMVAGame` never fire against
such an adversary. -/
def WellBehaved (secParam : ℕ) (A : AGMUFAdversary F G n) : Prop :=
  ∀ (sk : Key F n) (H : G) (pp : Params G n),
    Pr[⊥ | (simulateQ (guardedAgmOracleImpl gen secParam sk H pp) (A.run H pp)).run []] = 0 ∧
    ∀ z ∈ support (m := ProbComp)
        ((simulateQ (agmOracleImpl (gen := gen) secParam sk H pp) (A.run H pp)).run []),
      ForgeryConsistent gen H pp z

/-- The all-zero representation: every basis coefficient `0`, no tag coefficients. -/
def zeroRepr : AGMRepr F n := ⟨0, 0, 0, 0, 0, []⟩

/-- The trivial algebraic adversary: makes no oracle queries and outputs the zero forgery with
all-zero representations. It inhabits `WellBehaved` (`wellBehaved_trivialAdversary`). -/
noncomputable def trivialAdversary : AGMUFAdversary F G n where
  run := fun _ _ => pure (fun _ => 0, (0, 0), zeroRepr, zeroRepr)

/-- **`WellBehaved` is satisfiable** (for every `gen` and `secParam`): the guarded run of the
query-free `trivialAdversary` never fails, and its zero forgery is consistent (the all-zero
representation evaluates to `0` over any transcript basis). Statements conditional on
`WellBehaved` would be vacuous if the predicate were unsatisfiable; this lemma rules that
out. -/
lemma wellBehaved_trivialAdversary (secParam : ℕ) :
    WellBehaved gen secParam (trivialAdversary (F := F) (G := G) (n := n)) := by
  intro sk H pp
  constructor
  · simp [trivialAdversary, guardedAgmOracleImpl]
  · intro z hz
    simp only [trivialAdversary, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    -- `simp only`: the full simp set times out on `AddCommGroup F` instance search here.
    simp only [ForgeryConsistent, zeroRepr, AGMRepr.eval, List.zipWith_nil_left, List.sum_nil,
      zero_smul, Pi.zero_apply, Finset.sum_const_zero, add_zero, and_self]

/-! ## The forgetful translation to the plain game -/

/-- Translate instrumented queries to plain `UFQuery`s by dropping the representations: `sign`
and `verify` forward, `help` is answered locally by `false` (the plain game has no Help oracle;
`WellBehaved` rules out reachable `help` queries in the AGM game). `MsgVec crs` and `Tag crs` of
`μCMZBaseMACSyntax` unfold to `Fin n → F` and `G × G`, so queries and answers transport without
casts. -/
def forgetReprImpl {secParam : ℕ}
    (crs : (μCMZBaseMACSyntax F gen).Crs secParam n) :
    QueryImpl (AGMOracleSpec F G n)
      (OracleComp (UFOracleSpec (μCMZBaseMACSyntax F gen) crs))
  | .sign m => query (spec := UFOracleSpec (μCMZBaseMACSyntax F gen) crs) (UFQuery.sign m)
  | .verify m σ .. =>
      query (spec := UFOracleSpec (μCMZBaseMACSyntax F gen) crs) (UFQuery.verify m σ)
  | .help .. => pure false

/-- The body of `AGMUFAdversary.toUFAdversary` at the matching attribute count: run the
algebraic adversary with its queries translated by `forgetReprImpl`, then drop the forgery
representations from its output. -/
def AGMUFAdversary.toUFAdversaryBody {secParam : ℕ} (A : AGMUFAdversary F G n)
    (crs : (μCMZBaseMACSyntax F gen).Crs secParam n) (pp : (μCMZBaseMACSyntax F gen).Pp crs) :
    OracleComp (UFOracleSpec (μCMZBaseMACSyntax F gen) crs)
      ((μCMZBaseMACSyntax F gen).MsgVec crs × (μCMZBaseMACSyntax F gen).Tag crs) :=
  (fun out => (out.1, out.2.1)) <$> simulateQ (forgetReprImpl gen crs) (A.run crs pp)

/-- The forgetful translation of an algebraic adversary to a plain UF-CMVA adversary, from the
AGM game of §5.3 to the plain Figure 5 game: representations are dropped from queries and
output. `UFAdversary.run` quantifies over all attribute counts while the algebraic adversary is
fixed at `n`, so the translation runs `A` at `n` and outputs a junk forgery elsewhere. -/
def AGMUFAdversary.toUFAdversary (A : AGMUFAdversary F G n) :
    UFAdversary (μCMZBaseMACSyntax F gen) where
  run {_} {n'} crs pp :=
    if h : n' = n then by subst h; exact A.toUFAdversaryBody gen crs pp
    else pure (fun _ => (0 : F), ((0 : G), (0 : G)))

/-- Unfolding lemma for `AGMUFAdversary.toUFAdversary` at the matching attribute count: the
`dite` reduces to `AGMUFAdversary.toUFAdversaryBody`. -/
lemma AGMUFAdversary.toUFAdversary_run (A : AGMUFAdversary F G n) {secParam : ℕ}
    (crs : (μCMZBaseMACSyntax F gen).Crs secParam n) (pp : (μCMZBaseMACSyntax F gen).Pp crs) :
    (A.toUFAdversary gen).run crs pp = A.toUFAdversaryBody gen crs pp :=
  dif_pos rfl

end KVAC.Schemes.MicroCMZ
