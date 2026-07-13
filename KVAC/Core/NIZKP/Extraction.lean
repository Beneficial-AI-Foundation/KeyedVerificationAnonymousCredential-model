/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Security
import VCVio

/-!
# Knowledge soundness and simulation extractability (O24 §3.3)

The extraction-based security notions of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §3.3, on an
`NIZKPSyntax ProbComp`, following the game/advantage idiom of
`AlgebraicMAC/Security.lean` and the random-oracle setup of `Security.lean`.

O24 §3.3 (p. 25): a proof system is a knowledge-sound argument if there exists
an extractor Ext that takes as input the random coins and the code of the
p.p.t. adversary A (optionally a trapdoor for the crs, not required in the
paper's instantiations) such that, whenever A(crs) outputs (x, π), Ext outputs
w. The adversary wins if ZKP.V(crs, x, π) = 1 ∧ (x, w) ∉ R; the advantage is
Adv^ksnd_{ZKP,Ext,A}(λ).

The paper then announces a stronger notion for the MAC-unforgeability proofs:
the adversary may output simulated proofs and the extractor must provide, in
addition to the witness, a candidate statement (O24 §3.3, consumed in §§5.5 and
6.5). That notion is simulation extractability in the sense of Dao–Grubbs,
*Spartan and Bulletproofs are Simulation-Extractable (for Free!)*, IACR ePrint
2023/494, strengthened with the candidate statement.

## White-box extraction

The extractor here is **white-box**, following the paper literally (the
recorded decision of issue #43; the standard black-box rewindable convention
raised by Tom Shrimpton is a deliberate divergence). "Coins and code of A" is
modeled as:

- **code** — the extractor receives the adversary *value* itself, so it may
  inspect it as a term and re-run it at will (re-running on fresh randomness
  subsumes rewindable black-box access);
- **coins** — the extractor receives the observable trace of the concrete run
  it must extract from: the adversary's output (x, π) and the random-oracle
  transcript (`QueryCache`), and in the simulation-extractability game also the
  list of simulated proofs.

This is the interface the §5 reductions consume: the extractor is invoked once
per oracle query, straight-line, on the proof and the random-oracle trace
("it is possible to recover the statement from the actual proof by looking at
the trace of random oracle queries", §5.5), with the advantage terms entering
the bounds linearly. The optional crs trapdoor is omitted; the paper's
instantiations never use it (extraction is straight-line in the algebraic group
model, §9).

## Decidability hypotheses

The games decide the win condition, so they take decidability of the relation
(`RelationDecidable`) and, for freshness in simulation extractability,
decidable equality on statements and proofs (`StmtDecEq`, `ProofDecEq`). The
algebraic relations of the paper (R_cmz, R_bbs: group equations over ℤ_p)
satisfy all three.

## Layout

- `ROCache` — abbreviation for the random-oracle cache.
- `RelationDecidable`, `StmtDecEq`, `ProofDecEq` — decidability hypotheses.
- `KSNDAdversary` / `KSNDExtractor` — knowledge soundness: the adversary and
  the white-box extractor.
- `ksndGame` / `KSNDAdv` — the knowledge-soundness experiment and advantage.
- `SEQuery` / `SESpec` / `SEAdvSpec` — the simulation oracle arm.
- `SEAdversary` / `SEExtractor` — simulation extractability: the adversary and
  the white-box extractor returning a candidate statement.
- `SimLog` / `seOracleImpl` — the simulation oracle, logging the pairs (x, π)
  it returns.
- `seGame` / `SEAdv` — the simulation-extractability experiment and advantage.

A scheme is knowledge-sound (resp. simulation-extractable) if some extractor
makes the advantage negligible in `secParam` for every PPT adversary; the
asymptotic / negligibility statement is deferred, as for zero-knowledge and
UF-CMVA.
-/

namespace KVAC.Core

open OracleComp OracleSpec ENNReal

/-- The random-oracle cache of `H`: the state the lazy `randomOracle` threads
and the trace the white-box extractors receive. -/
abbrev ROCache (H : HashSpec) : Type := ((H.Dom →ₒ H.Rng).QueryCache)

/-- Decidability of the crs-indexed relation, needed to decide the win
condition (x, w) ∉ R of the extraction games. Holds for the paper's algebraic
relations (group equations over ℤ_p). -/
abbrev RelationDecidable (zkp : NIZKPSyntax ProbComp) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs)
    (w : zkp.Witness crs), Decidable (zkp.relation crs x w)

/-- Decidable equality on statements, needed for the freshness check and the
candidate-statement check of simulation extractability. -/
abbrev StmtDecEq (zkp : NIZKPSyntax ProbComp) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam), DecidableEq (zkp.Stmt crs)

/-- Decidable equality on proofs, needed for the freshness check of simulation
extractability. -/
abbrev ProofDecEq (zkp : NIZKPSyntax ProbComp) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam), DecidableEq (zkp.Proof crs)

/-- Whether an extraction attempt produced a witness for `x`: `false` when the
extractor returned `none`, otherwise whether the returned `w` satisfies the
relation. The extraction games win against exactly the runs where this is
`false` while the proof verifies. -/
def witnessValid (zkp : NIZKPSyntax ProbComp) (dec : RelationDecidable zkp)
    {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs) :
    Option (zkp.Witness crs) → Bool
  | none => false
  | some w => letI := dec crs x w; decide (zkp.relation crs x w)

/-! ## Knowledge soundness -/

/-- A knowledge-soundness adversary: given the crs, it queries the random
oracle (no other oracle: plain knowledge soundness gives A no simulated
proofs) and outputs a statement–proof pair (x, π).

Formalizes A of the knowledge-sound-argument definition, O24 §3.3. -/
structure KSNDAdversary (zkp : NIZKPSyntax ProbComp) (H : HashSpec) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (ZKRO H) (zkp.Stmt crs × zkp.Proof crs)

/-- A white-box knowledge-soundness extractor. Its inputs realize "the random
coins and the code of the p.p.t. adversary A" of O24 §3.3: the adversary value
(the code, inspectable and re-runnable), and the data of the concrete run to
extract from — the output pair (x, π) and the random-oracle transcript. The
optional crs trapdoor of the paper is omitted (unused by its instantiations).
Returns `none` when extraction fails.

The white-box (rather than black-box rewindable) interface is the recorded
decision of issue #43 and what the §5 reductions consume. -/
abbrev KSNDExtractor (zkp : NIZKPSyntax ProbComp) (H : HashSpec) : Type :=
  KSNDAdversary zkp H → {secParam : Nat} → (crs : zkp.Crs secParam) →
    zkp.Stmt crs → zkp.Proof crs → ROCache H →
    ProbComp (Option (zkp.Witness crs))

/-- The knowledge-soundness experiment as a `ProbComp Bool`. Runs the adversary
with a fresh random-oracle cache, hands the extractor the adversary, its
output, and the final cache, and returns `true` iff the proof verifies while
extraction failed to produce a witness for x.

Formalizes the O24 §3.3 experiment: crs ← ZKP.S(1^λ); (x, π) ← A(crs);
w ← Ext(coins, code of A); A wins if ZKP.V(crs, x, π) = 1 ∧ (x, w) ∉ R. The
verifier runs as the self-contained `ProbComp` of the carrier, independent of
the game's oracle cache, as everywhere in this layer. -/
def ksndGame (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (ext : KSNDExtractor zkp H) (A : KSNDAdversary zkp H)
    (dec : RelationDecidable zkp) (secParam : Nat) : ProbComp Bool := do
  let crs ← zkp.setup secParam
  let ((x, π), cache) ← (simulateQ (zkROImpl H) (A.run crs)).run ∅
  let w? ← ext A crs x π cache
  let v ← zkp.verify crs x π
  pure (v && !(witnessValid zkp dec crs x w?))

/-- The knowledge-soundness advantage of `A` with respect to extractor `ext`:
the probability that `ksndGame` returns `true`. A proof system is a
knowledge-sound argument if some `ext` makes this negligible in `secParam` for
every PPT `A`; the asymptotic statement is deferred.

Formalizes Adv^ksnd_{ZKP,Ext,A}(λ) of O24 §3.3. -/
noncomputable abbrev KSNDAdv (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (ext : KSNDExtractor zkp H) (A : KSNDAdversary zkp H)
    (dec : RelationDecidable zkp) (secParam : Nat) : ℝ≥0∞ :=
  Pr[= true | ksndGame zkp H ext A dec secParam]

/-! ## Simulation extractability -/

/-- The simulation oracle arm for a fixed crs: `sim x` requests a simulated
proof for the bare statement `x` — no witness, unlike `ZKQuery.prove`.

Formalizes the oracle giving the adversary "simulated proofs" in the stronger
notion of O24 §3.3 (Dao–Grubbs's SIM oracle, ePrint 2023/494). -/
inductive SEQuery (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : Type where
  | sim : zkp.Stmt crs → SEQuery zkp crs

/-- The `OracleSpec` of the simulation arm: `sim x` answers with a proof. -/
def SESpec (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : OracleSpec (SEQuery zkp crs)
  | .sim _ => zkp.Proof crs

/-- The full oracle interface a simulation-extractability adversary sees for a
fixed crs: the simulation arm together with `ZKRO`. -/
abbrev SEAdvSpec (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) (H : HashSpec) :
    OracleSpec (SEQuery zkp crs ⊕ (ℕ ⊕ H.Dom)) :=
  SESpec zkp crs + ZKRO H

/-- A simulation-extractability adversary: given the crs, it queries the
simulation oracle and the random oracle, and outputs a statement–proof pair
(x, π). -/
structure SEAdversary (zkp : NIZKPSyntax ProbComp) (H : HashSpec) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (SEAdvSpec zkp crs H) (zkp.Stmt crs × zkp.Proof crs)

/-- The list of statement–proof pairs the simulation oracle has returned so
far. Threaded through `seOracleImpl` and consulted at the end of the game for
the freshness of the adversary's output (the *strong* notion excludes exactly
the returned pairs, so a new proof of a queried statement still counts). -/
abbrev SimLog (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : Type :=
  List (zkp.Stmt crs × zkp.Proof crs)

/-- The state of the simulation-extractability game: the random-oracle cache
together with the simulation log. -/
abbrev SEState (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) (H : HashSpec) : Type :=
  ROCache H × SimLog zkp crs

/-- Implementation of the simulation-extractability oracles: the `sim` arm runs
the zero-knowledge simulator on the shared random-oracle cache (so it may
reprogram it) and logs the returned pair; the random-oracle arm runs `zkROImpl`
on the cache component and leaves the log unchanged. -/
def seOracleImpl (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (sim : ZKSimulator zkp H) {secParam : Nat} (crs : zkp.Crs secParam) :
    QueryImpl (SEAdvSpec zkp crs H) (StateT (SEState zkp crs H) ProbComp)
  | .inl (.sim x) => StateT.mk fun s => do
      let (π, cache) ← (sim crs x).run s.1
      pure (π, (cache, (x, π) :: s.2))
  | .inr q => StateT.mk fun s => do
      let (a, cache) ← (zkROImpl H q).run s.1
      pure (a, (cache, s.2))

/-- A white-box simulation-extractability extractor. Same white-box inputs as
`KSNDExtractor` — the adversary value, the output pair, the random-oracle
transcript — plus the simulation log, and its output carries, per O24's
stronger notion, a **candidate statement** in addition to the witness ("the
extractor has to provide (in addition to the witness) a candidate statement",
§3.3; the candidate instance Z of §§5.5 and 6.5, recoverable for Schnorr
proofs from the trace of random-oracle queries). Returns `none` when
extraction fails. -/
abbrev SEExtractor (zkp : NIZKPSyntax ProbComp) (H : HashSpec) : Type :=
  SEAdversary zkp H → {secParam : Nat} → (crs : zkp.Crs secParam) →
    zkp.Stmt crs → zkp.Proof crs → ROCache H → SimLog zkp crs →
    ProbComp (Option (zkp.Stmt crs × zkp.Witness crs))

/-- The strong-simulation-extractability experiment as a `ProbComp Bool`. Runs
the adversary with the simulation and random oracles over a fresh state, hands
the extractor the run's trace, and returns `true` iff the proof verifies, the
pair (x, π) is not among the simulated ones, and extraction failed — where
success demands the candidate statement match the adversary's (x̂ = x) and the
witness satisfy the relation.

Formalizes the stronger notion of O24 §3.3 (Dao–Grubbs ePrint 2023/494, with
O24's candidate statement): A^Sim(crs) outputs (x, π) and wins if
ZKP.V(crs, x, π) = 1 ∧ (x, π) ∉ Q_sim ∧ (x̂, w) ← Ext fails on x. -/
def seGame (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (sim : ZKSimulator zkp H) (ext : SEExtractor zkp H)
    (A : SEAdversary zkp H) (dec : RelationDecidable zkp)
    (ds : StmtDecEq zkp) (dp : ProofDecEq zkp) (secParam : Nat) :
    ProbComp Bool := do
  let crs ← zkp.setup secParam
  let ((x, π), (cache, log)) ←
    (simulateQ (seOracleImpl zkp H sim crs) (A.run crs)).run (∅, [])
  let r? ← ext A crs x π cache log
  let v ← zkp.verify crs x π
  letI := ds crs; letI := dp crs
  let fresh := decide ((x, π) ∉ log)
  let extracted := match r? with
    | none => false
    | some (x', w) => decide (x' = x) && witnessValid zkp dec crs x (some w)
  pure (v && fresh && !extracted)

/-- The simulation-extractability advantage of `A` with respect to simulator
`sim` and extractor `ext`: the probability that `seGame` returns `true`. A
proof system is (strongly) simulation-extractable if some `ext` makes this
negligible in `secParam` for every PPT `A`; the asymptotic statement is
deferred. This is the hypothesis the credential theorems consume (O24
Theorems 5.2, 5.3, 5.10, 5.11; cf. Remark 5.9 on when plain knowledge
soundness suffices). -/
noncomputable abbrev SEAdv (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (sim : ZKSimulator zkp H) (ext : SEExtractor zkp H)
    (A : SEAdversary zkp H) (dec : RelationDecidable zkp)
    (ds : StmtDecEq zkp) (dp : ProofDecEq zkp) (secParam : Nat) : ℝ≥0∞ :=
  Pr[= true | seGame zkp H sim ext A dec ds dp secParam]

end KVAC.Core
