/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.AlgebraicMAC.Security
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import KVAC.Schemes.MicroCMZ.SimulateQGuarded

/-!
# The AGM ↔ plain UF-CMVA bridge: `WellBehaved`

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

/-- The honest instrumented oracle asserting its own gate: behaves like `agmOracleImpl` while
every query is `agmGood`, aborts on the first bad one. -/
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
all-zero representations. Exists to witness `wellBehaved_trivialAdversary`. -/
noncomputable def trivialAdversary : AGMUFAdversary F G n where
  run := fun _ _ => pure (fun _ => 0, (0, 0), zeroRepr, zeroRepr)

/-- **`WellBehaved` is satisfiable** (for every `gen` and `secParam`): the guarded run of the
query-free `trivialAdversary` never fails, and its zero forgery is consistent (the all-zero
representation evaluates to `0` over any transcript basis). This inhabitant is the
non-vacuity guard for statements conditional on `WellBehaved`: should a future edit make
`WellBehaved` unsatisfiable, this lemma is what breaks. -/
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

end KVAC.Schemes.MicroCMZ
