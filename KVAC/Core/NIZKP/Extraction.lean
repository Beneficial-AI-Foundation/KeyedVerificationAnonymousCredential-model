/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Security

/-!
# Knowledge soundness and simulation extractability (O24 §3.3)

The two extraction-based notions of O24 §3.3 for an
`NIZKPSyntax (OracleComp (ZKRO H))`: the knowledge-soundness game and the strong
simulation-extractability game (Dao–Grubbs, IACR ePrint 2023/494, plus O24's
candidate statement).

Both extractors are white-box, following O24 §3.3 (p. 25) literally: Ext takes
the random coins and the code of the p.p.t. adversary A. The extractor
receives the adversary value (the code) and the run's trace (the output pair,
the random-oracle cache, and, for simulation extractability, the simulation
log). The optional crs trapdoor is omitted; the paper's instantiations never
use it. Issue #43 records this decision and the divergence from the black-box
rewindable convention.

The scheme is instantiated at the carrier `OracleComp (ZKRO H)`, so `verify`
runs through `zkROImpl` on the run's random-oracle cache and a Fiat–Shamir
verifier recomputes its challenge from the same oracle the proof was built
against. The design of this carrier and its `verify` underspecification are
recorded in `docs/DESIGN_ALTERNATIVES.md` (issue #101).

Game and advantage follow `AlgebraicMAC/Security.lean`; the random-oracle
setup follows `Security.lean`. Negligibility statements are deferred, as
everywhere in this layer.
-/

namespace KVAC.Core

open OracleComp OracleSpec ENNReal

/-- Decidable equality on statements, deciding freshness and the
candidate-statement check of the O24 §3.3 simulation-extractability game. -/
abbrev NIZKPSyntax.DecidableEqStmt (H : HashSpec)
    (zkp : NIZKPSyntax (OracleComp (ZKRO H))) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam), DecidableEq (zkp.Stmt crs)

/-- Decidable equality on proofs, deciding freshness in the O24 §3.3
simulation-extractability game. -/
abbrev NIZKPSyntax.DecidableEqProof (H : HashSpec)
    (zkp : NIZKPSyntax (OracleComp (ZKRO H))) : Type :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam), DecidableEq (zkp.Proof crs)

/-- `true` iff the extractor returned a witness satisfying the relation. The
O24 §3.3 games win for the adversary when this fails on a verifying proof. -/
def witnessValid (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (dec : zkp.DecidableRelation) {secParam : Nat} (crs : zkp.Crs secParam)
    (x : zkp.Stmt crs) : Option (zkp.Witness crs) → Bool
  | none => false
  | some w => letI := dec crs x w; decide (zkp.relation crs x w)

/-! ## Knowledge soundness -/

/-- The knowledge-soundness adversary A(crs) of O24 §3.3: outputs a pair
(x, π) with random-oracle access. -/
structure KSNDAdversary (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (ZKRO H) (zkp.Stmt crs × zkp.Proof crs)

/-- The white-box extractor Ext of O24 §3.3. The coins and code of A enter as
the adversary value and its run's trace, the output (x, π) and the
random-oracle cache. Returns `none` on failure. -/
abbrev KSNDExtractor (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) : Type :=
  KSNDAdversary H zkp → {secParam : Nat} → (crs : zkp.Crs secParam) →
    zkp.Stmt crs → zkp.Proof crs → H.Cache →
    ProbComp (Option (zkp.Witness crs))

/-- The knowledge-soundness experiment of O24 §3.3: crs ← ZKP.S(1^λ);
(x, π) ← A(crs); w ← Ext; A wins iff ZKP.V(crs, x, π) = 1 ∧ (x, w) ∉ R. One
cache is threaded through `setup`, the adversary, and `verify`, so `verify`
runs against the adversary's final cache. -/
def ksndGame (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (ext : KSNDExtractor H zkp) (A : KSNDAdversary H zkp)
    (dec : zkp.DecidableRelation) (secParam : Nat) : ProbComp Bool := do
  let (crs, c0) ← (simulateQ (zkROImpl H) (zkp.setup secParam)).run ∅
  let ((x, π), c1) ← (simulateQ (zkROImpl H) (A.run crs)).run c0
  let w? ← ext A crs x π c1
  let (v, _) ← (simulateQ (zkROImpl H) (zkp.verify crs x π)).run c1
  pure (v && !(witnessValid H zkp dec crs x w?))

/-- Adv^ksnd_{ZKP,Ext,A}(λ) of O24 §3.3: the probability that `ksndGame`
returns `true`. -/
noncomputable abbrev KSNDAdv (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (ext : KSNDExtractor H zkp) (A : KSNDAdversary H zkp)
    (dec : zkp.DecidableRelation) (secParam : Nat) : ℝ≥0∞ :=
  Pr[= true | ksndGame H zkp ext A dec secParam]

/-! ## Simulation extractability -/

/-- The simulation-oracle arm of the O24 §3.3 stronger notion: `sim x`
requests a simulated proof for the bare statement, no witness. -/
inductive SEQuery (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    {secParam : Nat} (crs : zkp.Crs secParam) : Type where
  | sim : zkp.Stmt crs → SEQuery H zkp crs

/-- `OracleSpec` of the O24 §3.3 simulation arm: `sim x` answers with a
proof. -/
def SESpec (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    {secParam : Nat} (crs : zkp.Crs secParam) : OracleSpec (SEQuery H zkp crs)
  | .sim _ => zkp.Proof crs

/-- Oracle interface of an O24 §3.3 simulation-extractability adversary: the
simulation arm together with `ZKRO`. -/
abbrev SEAdvSpec (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    {secParam : Nat} (crs : zkp.Crs secParam) :
    OracleSpec (SEQuery H zkp crs ⊕ (ℕ ⊕ H.Dom)) :=
  SESpec H zkp crs + ZKRO H

/-- The simulation-extractability adversary A^Sim(crs) of O24 §3.3: outputs a
pair (x, π). -/
structure SEAdversary (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (SEAdvSpec H zkp crs) (zkp.Stmt crs × zkp.Proof crs)

/-- Pairs returned by the simulation oracle. The strong freshness check of the
O24 §3.3 game excludes exactly these. -/
abbrev SimLog (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    {secParam : Nat} (crs : zkp.Crs secParam) : Type :=
  List (zkp.Stmt crs × zkp.Proof crs)

/-- State of the O24 §3.3 simulation-extractability game: the random-oracle
cache and the simulation log. -/
abbrev SEState (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    {secParam : Nat} (crs : zkp.Crs secParam) : Type :=
  H.Cache × SimLog H zkp crs

/-- Implementation of the O24 §3.3 simulation-extractability oracles: `sim`
runs the zero-knowledge simulator on the shared cache (so it may reprogram it)
and logs the returned pair; the random-oracle arm updates the cache. -/
def seOracleImpl (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (sim : ZKSimulator H zkp) {secParam : Nat} (crs : zkp.Crs secParam) :
    QueryImpl (SEAdvSpec H zkp crs) (StateT (SEState H zkp crs) ProbComp)
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
abbrev SEExtractor (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) : Type :=
  SEAdversary H zkp → {secParam : Nat} → (crs : zkp.Crs secParam) →
    zkp.Stmt crs → zkp.Proof crs → H.Cache → SimLog H zkp crs →
    ProbComp (Option (zkp.Stmt crs × zkp.Witness crs))

/-- The strong simulation-extractability experiment of O24 §3.3 (Dao–Grubbs,
IACR ePrint 2023/494, plus the candidate statement): A^Sim(crs) outputs
(x, π) and wins iff ZKP.V(crs, x, π) = 1, (x, π) is not among the simulated
pairs, and extraction fails, where success demands x̂ = x and (x, w) ∈ R.
`verify` runs through `zkROImpl` on the run's final random-oracle cache. -/
def seGame (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (sim : ZKSimulator H zkp) (ext : SEExtractor H zkp)
    (A : SEAdversary H zkp) (dec : zkp.DecidableRelation)
    (ds : zkp.DecidableEqStmt) (dp : zkp.DecidableEqProof) (secParam : Nat) :
    ProbComp Bool := do
  let (crs, c0) ← (simulateQ (zkROImpl H) (zkp.setup secParam)).run ∅
  let ((x, π), (cache, log)) ←
    (simulateQ (seOracleImpl H zkp sim crs) (A.run crs)).run (c0, [])
  let r? ← ext A crs x π cache log
  let (v, _) ← (simulateQ (zkROImpl H) (zkp.verify crs x π)).run cache
  letI := ds crs; letI := dp crs
  let fresh := decide ((x, π) ∉ log)
  let extracted := match r? with
    | none => false
    | some (x', w) => decide (x' = x) && witnessValid H zkp dec crs x (some w)
  pure (v && fresh && !extracted)

/-- The simulation-extractability advantage of the O24 §3.3 stronger notion:
the probability that `seGame` returns `true`. The hypothesis the μCMZ and μBBS
credential theorems consume. -/
noncomputable abbrev SEAdv (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (sim : ZKSimulator H zkp) (ext : SEExtractor H zkp)
    (A : SEAdversary H zkp) (dec : zkp.DecidableRelation)
    (ds : zkp.DecidableEqStmt) (dp : zkp.DecidableEqProof) (secParam : Nat) : ℝ≥0∞ :=
  Pr[= true | seGame H zkp sim ext A dec ds dp secParam]

end KVAC.Core
