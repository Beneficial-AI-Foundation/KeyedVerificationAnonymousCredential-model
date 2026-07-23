/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Security
import VCVio

/-!
# Knowledge soundness and simulation extractability (O24 §3.3)

The two extraction-based notions of O24 §3.3 for an `NIZKPSyntax ProbComp`:
the knowledge-soundness game and the strong simulation-extractability game
(Dao–Grubbs, IACR ePrint 2023/494, plus O24's candidate statement).

Both extractors are white-box, following O24 §3.3 (p. 25) literally: Ext takes
the random coins and the code of the p.p.t. adversary A. The extractor
receives the adversary value (the code) and the run's trace (the output pair,
the random-oracle cache, and, for simulation extractability, the simulation
log). The optional crs trapdoor is omitted; the paper's instantiations never
use it. Issue #43 records this decision and the divergence from the black-box
rewindable convention.

Game and advantage follow `AlgebraicMAC/Security.lean`; the random-oracle
setup follows `Security.lean`. Negligibility statements are deferred, as
everywhere in this layer.
-/

namespace KVAC.Core

open OracleComp OracleSpec ENNReal

/-- Random-oracle cache of `H`: the trace handed to the O24 §3.3 white-box
extractors. -/
abbrev ROCache (H : HashSpec) : Type := ((H.Dom →ₒ H.Rng).QueryCache)

/-- Decidable equality on statements, deciding freshness and the
candidate-statement check of the O24 §3.3 simulation-extractability game. -/
abbrev StmtDecEq (zkp : NIZKPSyntax ProbComp) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam), DecidableEq (zkp.Stmt crs)

/-- Decidable equality on proofs, deciding freshness in the O24 §3.3
simulation-extractability game. -/
abbrev ProofDecEq (zkp : NIZKPSyntax ProbComp) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam), DecidableEq (zkp.Proof crs)

/-- `true` iff the extractor returned a witness satisfying the relation. The
O24 §3.3 games win for the adversary when this fails on a verifying proof. -/
def witnessValid (zkp : NIZKPSyntax ProbComp) (dec : zkp.DecidableRelation)
    {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs) :
    Option (zkp.Witness crs) → Bool
  | none => false
  | some w => letI := dec crs x w; decide (zkp.relation crs x w)

/-! ## Knowledge soundness -/

/-- The knowledge-soundness adversary A(crs) of O24 §3.3: outputs a pair
(x, π) with random-oracle access. -/
structure KSNDAdversary (zkp : NIZKPSyntax ProbComp) (H : HashSpec) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (ZKRO H) (zkp.Stmt crs × zkp.Proof crs)

/-- The white-box extractor Ext of O24 §3.3. The coins and code of A enter as
the adversary value and its run's trace, the output (x, π) and the
random-oracle cache. Returns `none` on failure. -/
abbrev KSNDExtractor (zkp : NIZKPSyntax ProbComp) (H : HashSpec) : Type :=
  KSNDAdversary zkp H → {secParam : Nat} → (crs : zkp.Crs secParam) →
    zkp.Stmt crs → zkp.Proof crs → ROCache H →
    ProbComp (Option (zkp.Witness crs))

/-- The knowledge-soundness experiment of O24 §3.3: crs ← ZKP.S(1^λ);
(x, π) ← A(crs); w ← Ext; A wins iff ZKP.V(crs, x, π) = 1 ∧ (x, w) ∉ R. -/
def ksndGame (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (ext : KSNDExtractor zkp H) (A : KSNDAdversary zkp H)
    (dec : zkp.DecidableRelation) (secParam : Nat) : ProbComp Bool := do
  let crs ← zkp.setup secParam
  let ((x, π), cache) ← (simulateQ (zkROImpl H) (A.run crs)).run ∅
  let w? ← ext A crs x π cache
  let v ← zkp.verify crs x π
  pure (v && !(witnessValid zkp dec crs x w?))

/-- Adv^ksnd_{ZKP,Ext,A}(λ) of O24 §3.3: the probability that `ksndGame`
returns `true`. -/
noncomputable abbrev KSNDAdv (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (ext : KSNDExtractor zkp H) (A : KSNDAdversary zkp H)
    (dec : zkp.DecidableRelation) (secParam : Nat) : ℝ≥0∞ :=
  Pr[= true | ksndGame zkp H ext A dec secParam]

/-! ## Simulation extractability -/

/-- The simulation-oracle arm of the O24 §3.3 stronger notion: `sim x`
requests a simulated proof for the bare statement, no witness. -/
inductive SEQuery (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : Type where
  | sim : zkp.Stmt crs → SEQuery zkp crs

/-- `OracleSpec` of the O24 §3.3 simulation arm: `sim x` answers with a
proof. -/
def SESpec (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : OracleSpec (SEQuery zkp crs)
  | .sim _ => zkp.Proof crs

/-- Oracle interface of an O24 §3.3 simulation-extractability adversary: the
simulation arm together with `ZKRO`. -/
abbrev SEAdvSpec (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) (H : HashSpec) :
    OracleSpec (SEQuery zkp crs ⊕ (ℕ ⊕ H.Dom)) :=
  SESpec zkp crs + ZKRO H

/-- The simulation-extractability adversary A^Sim(crs) of O24 §3.3: outputs a
pair (x, π). -/
structure SEAdversary (zkp : NIZKPSyntax ProbComp) (H : HashSpec) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (SEAdvSpec zkp crs H) (zkp.Stmt crs × zkp.Proof crs)

/-- Pairs returned by the simulation oracle. The strong freshness check of the
O24 §3.3 game excludes exactly these. -/
abbrev SimLog (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : Type :=
  List (zkp.Stmt crs × zkp.Proof crs)

/-- State of the O24 §3.3 simulation-extractability game: the random-oracle
cache and the simulation log. -/
abbrev SEState (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) (H : HashSpec) : Type :=
  ROCache H × SimLog zkp crs

/-- Implementation of the O24 §3.3 simulation-extractability oracles: `sim`
runs the zero-knowledge simulator on the shared cache (so it may reprogram it)
and logs the returned pair; the random-oracle arm updates the cache. -/
def seOracleImpl (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (sim : ZKSimulator zkp H) {secParam : Nat} (crs : zkp.Crs secParam) :
    QueryImpl (SEAdvSpec zkp crs H) (StateT (SEState zkp crs H) ProbComp)
  | .inl (.sim x) => StateT.mk fun s => do
      let (π, cache) ← (sim crs x).run s.1
      pure (π, (cache, (x, π) :: s.2))
  | .inr q => StateT.mk fun s => do
      let (a, cache) ← (zkROImpl H q).run s.1
      pure (a, (cache, s.2))

/-- The white-box extractor of the O24 §3.3 stronger notion: the
`KSNDExtractor` inputs plus the simulation log, returning a candidate
statement in addition to the witness (the candidate instance Z of the
extractability proofs). Returns `none` on failure. -/
abbrev SEExtractor (zkp : NIZKPSyntax ProbComp) (H : HashSpec) : Type :=
  SEAdversary zkp H → {secParam : Nat} → (crs : zkp.Crs secParam) →
    zkp.Stmt crs → zkp.Proof crs → ROCache H → SimLog zkp crs →
    ProbComp (Option (zkp.Stmt crs × zkp.Witness crs))

/-- The strong simulation-extractability experiment of O24 §3.3 (Dao–Grubbs,
IACR ePrint 2023/494, plus the candidate statement): A^Sim(crs) outputs
(x, π) and wins iff ZKP.V(crs, x, π) = 1, (x, π) is not among the simulated
pairs, and extraction fails, where success demands x̂ = x and (x, w) ∈ R. -/
def seGame (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (sim : ZKSimulator zkp H) (ext : SEExtractor zkp H)
    (A : SEAdversary zkp H) (dec : zkp.DecidableRelation)
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

/-- The simulation-extractability advantage of the O24 §3.3 stronger notion:
the probability that `seGame` returns `true`. The hypothesis the μCMZ and μBBS
credential theorems consume. -/
noncomputable abbrev SEAdv (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (sim : ZKSimulator zkp H) (ext : SEExtractor zkp H)
    (A : SEAdversary zkp H) (dec : zkp.DecidableRelation)
    (ds : StmtDecEq zkp) (dp : ProofDecEq zkp) (secParam : Nat) : ℝ≥0∞ :=
  Pr[= true | seGame zkp H sim ext A dec ds dp secParam]

end KVAC.Core
