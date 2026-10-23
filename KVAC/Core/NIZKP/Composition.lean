/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Extraction
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Trace extractors

The knowledge-soundness extractor of §3.3 (p. 26) is white-box. It "takes as
input the random coins and the code of the p.p.t. adversary A", and
`KSNDExtractor` takes the adversary value as its first argument. The proof of
Theorem 5.8 (§5.4, p. 40) has the simulator `Sim.I` invoke the extractor on the
issuer's proof `π_is`. `Sim.I` runs inside the anonymity game, where it holds
the issuer's message and the random-oracle table and nothing else, and
Definition 4.4 fixes `Sim` before the adversary, so there is no adversary for
`Sim.I` to hand to a `KSNDExtractor`. Sections 2.6 (p. 21) and 9 (p. 77) name
straight-line extraction as the notion credentials need, while Theorem 5.8
prints the §3.3 advantage `Adv^ksnd`.

A `TraceExtractor` is what `Sim.I` can call. It is a function of the crs, the
statement, the proof and the random-oracle table, the partial map from queried
points to their answers. It never reruns the adversary. The map `toKSND` makes a
trace extractor a `KSNDExtractor` that ignores the adversary, so the printed
`Adv^ksnd` is defined for it and the bound of Theorem 5.8 keeps its printed
form. The lemma `KnowledgeSound.of_trace` states that knowledge soundness with a
trace extractor implies the §3.3 notion. Extractors carry no running-time bound,
so the converse holds as well. An extractor that chooses a witness whenever one
exists is a trace extractor, and its advantage is at most that of any white-box
extractor. The trace form is therefore a modelling discipline, not a stronger
hypothesis, as long as `OracleComp` carries no cost model, which issue #148
lists as out of scope.
The §9 extractor never rewinds. It also reads the algebraic representations of
Equation 41 (p. 78), which the table does not hold, so the instantiation of
issue #3 must carry them in the proof or in the table.
-/

namespace KVAC.Core

open OracleComp OracleSpec ENNReal

/-! ## Trace extractors -/

/-- An extractor from the crs, the statement, the proof and the random-oracle
table as of the end of the adversary's run. Unlike
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

/-- Knowledge soundness with a trace extractor, the hypothesis that the
anonymity simulator of §5.4 needs. -/
def TraceKnowledgeSound (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H)))
    (dec : zkp.DecidableRelation) (isPPT : KSNDAdversary H zkp → Prop) : Prop :=
  ∃ e : TraceExtractor H zkp, KnowledgeSoundWith H zkp dec isPPT e.toKSND

/-- A trace extractor is a §3.3 extractor, so knowledge soundness with a trace
extractor implies the §3.3 notion. -/
theorem KnowledgeSound.of_trace {H : HashSpec} {zkp : NIZKPSyntax (OracleComp (ZKRO H))}
    {dec : zkp.DecidableRelation} {isPPT : KSNDAdversary H zkp → Prop}
    (h : TraceKnowledgeSound H zkp dec isPPT) : KnowledgeSound H zkp dec isPPT :=
  let ⟨e, he⟩ := h
  ⟨e.toKSND, he⟩

end KVAC.Core
