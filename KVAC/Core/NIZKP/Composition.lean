/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Extraction
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Knowledge soundness in the presence of other simulated proofs (O24 Remark 5.9)

Hybrid H3 of O24 Theorem 5.8 (§5.4, p. 41) extracts from a proof `π_is` that
the issuer produced after receiving a simulated `π_iu`. The §3.3 game
`ksndGame` offers the adversary no simulated proofs, so the property H3 uses is
`KSNDSimAdv`, knowledge soundness with a simulation oracle for another
proof system over the same random oracle. Remark 5.9 (§5.4, p. 42) names the
mirror case, `π_iu` after simulated `π_is`, the case of Theorem 5.10, and
asserts that knowledge soundness suffices for Schnorr proofs because "the
vector sizes mismatch". The lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated`
states that assertion for any proof system, with the mismatch as disjoint
regions of the random-oracle domain, `ConfinedSystem` and `DomainSeparated`.
Hybrid H2 needs the same condition, since its reduction runs the simulator of
`ZKP_cmz.iu` inside the zero-knowledge game of `ZKP_cmz.p`.

## Trace extractors

The knowledge-soundness extractor of §3.3 (p. 26) is white-box. It "takes as
input the random coins and the code of the p.p.t. adversary A", and
`KSNDExtractor` takes the adversary value as its first argument. The proof of
Theorem 5.8 (§5.4, p. 40) has the simulator `Sim.I` invoke the extractor on the
issuer's proof `π_is`. `Sim.I` runs inside the anonymity game, where it holds
the issuer's message and the random-oracle table and nothing else, and
Definition 4.4 fixes `Sim` before the adversary, so there is no adversary for
`Sim.I` to hand to a `KSNDExtractor`. The paper leaves this gap open.

A `TraceExtractor` is what `Sim.I` can call. It is a function of the trace of
the run, the crs, the statement, the proof and the random-oracle table, which
records every query and answer, the programmed points included. It never reruns
the adversary. `toKSND` makes a trace extractor a `KSNDExtractor` that ignores
the adversary, so the printed `Adv^ksnd` is defined for it and the bound of
Theorem 5.8 keeps its printed form. The lemma `KnowledgeSound.of_trace` states
that knowledge soundness with a trace extractor implies the §3.3 notion. The
converse fails, a white-box extractor need not be a trace extractor, so the
theorem assumes more than §3.3 states.
The paper's own extractors have this form. For Schnorr proofs the statement is
recovered "by looking at the trace of random oracle queries" (§5.5, p. 42), and
the §9 extractor never rewinds. The §9 extractor also reads the algebraic
representations of Equation 41 (p. 78), which the trace does not hold, so the
instantiation of issue #3 must carry them in the proof or in the table.
-/

namespace KVAC.Core

open OracleComp OracleSpec ENNReal

/-! ## Trace extractors -/

/-- An extractor from the trace of a run, the crs, the statement, the proof and
the random-oracle table as of the end of the adversary's run. Unlike
`KSNDExtractor` it does not receive the adversary, so the simulator of Theorem
5.8 can call it. See the module docstring. -/
abbrev TraceExtractor (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) : Type :=
  {secParam : Nat} → (crs : zkp.Crs secParam) → zkp.Stmt crs → zkp.Proof crs → H.Cache →
    ProbComp (Option (zkp.Witness crs))

/-- A trace extractor as a `KSNDExtractor` that ignores the adversary, so that the
printed `Adv^ksnd` applies to it. -/
def TraceExtractor.toKSND {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    (e : TraceExtractor H zkp) : KSNDExtractor H zkp :=
  fun _ => e

/-- Knowledge soundness of O24 §3.3 (p. 26) with a given extractor. For every
adversary the efficiency predicate admits, the advantage is negligible in the
security parameter. -/
def KnowledgeSoundWith (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (dec : zkp.DecidableRelation) (isPPT : KSNDAdversary H zkp → Prop)
    (ext : KSNDExtractor H zkp) : Prop :=
  ∀ A : KSNDAdversary H zkp, isPPT A → negligible fun secParam => KSNDAdv H zkp ext A dec secParam

/-- Knowledge soundness of O24 §3.3 (p. 26), "there exists an extractor Ext". -/
def KnowledgeSound (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (dec : zkp.DecidableRelation) (isPPT : KSNDAdversary H zkp → Prop) : Prop :=
  ∃ ext : KSNDExtractor H zkp, KnowledgeSoundWith H zkp dec isPPT ext

/-- Knowledge soundness with a trace extractor, the hypothesis the simulator of
O24 Theorem 5.8 needs. -/
def TraceKnowledgeSound (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (dec : zkp.DecidableRelation) (isPPT : KSNDAdversary H zkp → Prop) : Prop :=
  ∃ e : TraceExtractor H zkp, KnowledgeSoundWith H zkp dec isPPT e.toKSND

/-- A trace extractor is a §3.3 extractor, so knowledge soundness with a trace
extractor implies the §3.3 notion. The converse does not follow. -/
theorem KnowledgeSound.of_trace {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    {dec : zkp.DecidableRelation} {isPPT : KSNDAdversary H zkp → Prop}
    (h : TraceKnowledgeSound H zkp dec isPPT) : KnowledgeSound H zkp dec isPPT :=
  let ⟨e, he⟩ := h
  ⟨e.toKSND, he⟩

/-! ## The simulation oracle -/

/-- A simulation oracle for proof systems other than `zkp`, over the shared
random-oracle cache, so that it may reprogram the table as a `ZKSimulator`
does. The queries are statements of the other relations and the answers their
simulated proofs. It is indexed by the crs of `zkp`, which the proof systems of
O24 Figure 9 share. -/
structure SimulationOracle (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) where
  /-- The query type. -/
  Query : {secParam : Nat} → zkp.Crs secParam → Type
  /-- The oracle signature. -/
  spec : {secParam : Nat} → (crs : zkp.Crs secParam) → OracleSpec (Query crs)
  /-- The simulators of the other proof systems. -/
  impl : {secParam : Nat} → (crs : zkp.Crs secParam) →
    QueryImpl (spec crs) (StateT H.Cache ProbComp)

/-- The simulation oracle together with `ZKRO`. -/
abbrev KSNDSimSpec (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (simOracle : SimulationOracle H zkp) {secParam : Nat} (crs : zkp.Crs secParam) :
    OracleSpec (simOracle.Query crs ⊕ (ℕ ⊕ H.Dom)) :=
  simOracle.spec crs + ZKRO H

/-- The adversary of `ksndSimGame`. It outputs a statement and a proof for `zkp`
with access to the simulation oracle and the random oracle. -/
structure KSNDSimAdversary (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (simOracle : SimulationOracle H zkp) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (KSNDSimSpec H zkp simOracle crs) (zkp.Stmt crs × zkp.Proof crs)

/-- `ksndGame` with the simulation oracle added to the adversary's
interface, the property hybrid H3 of O24 Theorem 5.8 uses. The extractor and
`verify` receive the cache as of the end of the adversary's run, including the
points the simulators of the other systems programmed. -/
def ksndSimGame (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (simOracle : SimulationOracle H zkp) (e : TraceExtractor H zkp)
    (A : KSNDSimAdversary H zkp simOracle) (dec : zkp.DecidableRelation) (secParam : Nat) :
    ProbComp Bool := do
  let (crs, c0) ← (simulateQ (zkROImpl H) (zkp.setup secParam)).run ∅
  let ((x, π), c1) ← (simulateQ (simOracle.impl crs + zkROImpl H) (A.run crs)).run c0
  let w? ← e crs x π c1
  let (v, _) ← (simulateQ (zkROImpl H) (zkp.verify crs x π)).run c1
  pure (v && !(witnessValid H zkp dec crs x w?))

/-- The probability that `ksndSimGame` returns `true`. -/
noncomputable abbrev KSNDSimAdv (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (simOracle : SimulationOracle H zkp) (e : TraceExtractor H zkp)
    (A : KSNDSimAdversary H zkp simOracle) (dec : zkp.DecidableRelation) (secParam : Nat) :
    ℝ≥0∞ :=
  Pr[= true | ksndSimGame H zkp simOracle e A dec secParam]

/-! ## Domain separation, the condition of Remark 5.9 -/

/-- A region of the random-oracle domain. -/
abbrev Region (H : HashSpec) : Type := H.Dom → Bool

namespace Region

variable {H : HashSpec}

/-- The cache restricted to the region. Points outside it read `none`. -/
def restrict (P : Region H) (c : H.Cache) : H.Cache :=
  fun t => if P t then c t else none

/-- The cache that reads `c₁` inside the region and `c₂` outside it. -/
def merge (P : Region H) (c₁ c₂ : H.Cache) : H.Cache :=
  fun t => if P t then c₁ t else c₂ t

/-- Two caches agree outside the region. -/
def AgreeOutside (P : Region H) (c d : H.Cache) : Prop :=
  ∀ t, P t = false → c t = d t

/-- Two regions share no point. -/
def Disjoint (P Q : Region H) : Prop :=
  ∀ t, P t = true → Q t = false

/-- A computation is confined to the region when it reads the cache inside the
region only and writes nothing outside it. -/
def Confined (P : Region H) {α : Type} (m : StateT H.Cache ProbComp α) : Prop :=
  ∀ c, m.run c = (m.run (P.restrict c) >>= fun ac => pure (ac.1, P.merge ac.2 c))

/-- Run an implementation on the region's part of the cache only. -/
def liftImpl (P : Region H) {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT H.Cache ProbComp)) :
    QueryImpl spec (StateT H.Cache ProbComp) :=
  fun q => StateT.mk fun c => do
    let (a, c') ← (impl q).run (P.restrict c)
    pure (a, P.merge c' c)

end Region

/-- A trace extractor that reads the region only. -/
def TraceExtractor.ConfinedTo {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    (e : TraceExtractor H zkp) (P : Region H) : Prop :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs) (π : zkp.Proof crs)
    (c : H.Cache), e crs x π c = e crs x π (P.restrict c)

/-- A proof system whose setup, prover and verifier are confined to a region,
the "different random oracles" of O24 Remark 5.9 within one oracle. For a
Fiat–Shamir Σ-protocol the region is the transcript hashes of its statement
shape. -/
structure ConfinedSystem (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (P : Region H) : Prop where
  /-- Setup is confined. -/
  setup_confined : ∀ secParam : Nat, P.Confined (simulateQ (zkROImpl H) (zkp.setup secParam))
  /-- The prover is confined. -/
  prove_confined : ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs)
    (w : zkp.Witness crs), P.Confined (simulateQ (zkROImpl H) (zkp.prove crs x w))
  /-- The verifier is confined. -/
  verify_confined : ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs)
    (π : zkp.Proof crs), P.Confined (simulateQ (zkROImpl H) (zkp.verify crs x π))

/-- A zero-knowledge simulator confined to a region. -/
def ZKSimulatorConfinedTo {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    (sim : ZKSimulator H zkp) (P : Region H) : Prop :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs), P.Confined (sim crs x)

/-- The condition of O24 Remark 5.9. The simulators of the other systems are confined to one
region, and setup, the verifier and the extractor of `zkp` to a disjoint one.
The Remark's "vector sizes mismatch" is the disjointness. -/
structure DomainSeparated (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (simOracle : SimulationOracle H zkp) (e : TraceExtractor H zkp) where
  /-- The region of the simulators of the other systems. -/
  simRegion : Region H
  /-- The region of `zkp`. -/
  region : Region H
  /-- The regions share no point. -/
  disjoint : simRegion.Disjoint region
  /-- The simulators of the other systems are confined to their region. -/
  sim_confined : ∀ {secParam : Nat} (crs : zkp.Crs secParam) (q : simOracle.Query crs),
    simRegion.Confined (simOracle.impl crs q)
  /-- Setup is confined to the region of `zkp`. -/
  setup_confined : ∀ secParam : Nat,
    region.Confined (simulateQ (zkROImpl H) (zkp.setup secParam))
  /-- The verifier is confined to the region of `zkp`. -/
  verify_confined : ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs)
    (π : zkp.Proof crs), region.Confined (simulateQ (zkROImpl H) (zkp.verify crs x π))
  /-- The extractor reads the region of `zkp` only. -/
  ext_confined : e.ConfinedTo region

/-! ## The reduction of Remark 5.9 -/

/-- The random-oracle arm of the reduction. Queries inside the region go to a
lazy random oracle on the local table, every other query to the game's oracle. -/
def regionROImpl (H : HashSpec) (P : Region H) :
    QueryImpl (ZKRO H) (StateT H.Cache (OracleComp (ZKRO H)))
  | .inl i => StateT.mk fun loc => do
      let a ← query (spec := ZKRO H) (.inl i)
      pure (a, loc)
  | .inr t => StateT.mk fun loc =>
      if P t then do
        let (a, loc') ← liftM ((H.roImpl t).run loc)
        pure (a, loc')
      else do
        let a ← query (spec := ZKRO H) (.inr t)
        pure (a, loc)

/-- The simulation-oracle arm of the reduction. The simulators of the other
systems run on the local table. -/
def simulationOracleImpl {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    (simOracle : SimulationOracle H zkp) {secParam : Nat} (crs : zkp.Crs secParam) :
    QueryImpl (simOracle.spec crs) (StateT H.Cache (OracleComp (ZKRO H))) :=
  fun q => StateT.mk fun loc => liftM ((simOracle.impl crs q).run loc)

/-- The reduction `A″` of O24 Remark 5.9. It runs the adversary with the simulation oracle
with the simulation region served from a local table that starts empty. -/
def KSNDSimAdversary.toKSND {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    {simOracle : SimulationOracle H zkp} {e : TraceExtractor H zkp}
    (A : KSNDSimAdversary H zkp simOracle) (ds : DomainSeparated H zkp simOracle e) :
    KSNDAdversary H zkp where
  run crs :=
    (simulateQ (simulationOracleImpl simOracle crs + regionROImpl H ds.simRegion)
      (A.run crs)).run' ∅

/-- **O24 Remark 5.9.** Under domain separation, knowledge soundness suffices.
The advantage in `ksndSimGame` is bounded by the printed `Adv^ksnd` of the
reduction `A.toKSND ds`. -/
theorem ksndSimAdv_le_ksndAdv_of_domainSeparated (H : HashSpec)
    (zkp : NIZKPSyntax (OracleComp (ZKRO H))) (simOracle : SimulationOracle H zkp)
    (e : TraceExtractor H zkp) (ds : DomainSeparated H zkp simOracle e)
    (A : KSNDSimAdversary H zkp simOracle) (dec : zkp.DecidableRelation) (secParam : Nat) :
    KSNDSimAdv H zkp simOracle e A dec secParam ≤
      KSNDAdv H zkp e.toKSND (A.toKSND ds) dec secParam := by
  sorry

end KVAC.Core
