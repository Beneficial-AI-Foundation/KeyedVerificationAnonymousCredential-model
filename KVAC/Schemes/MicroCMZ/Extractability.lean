/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Credential

import KVAC.Schemes.MicroCMZ.UFCMVAHelp
import KVAC.Framework.Extractability
import KVAC.Core.NIZKP.Composition

/-!
# Extractability of μCMZ (O24 §5.5, Theorem 5.10)

The statement of O24 Theorem 5.10 for `μCMZCredentialSyntax` of Figure 9,
with the extractor `Ext = (Ext.I, Ext.P)` of its proof (§5.5, p. 42). The
proof is deferred. The sections below hold, in order, the three proof systems
as §3.3 objects at the sampled crs, the extractors and the simulator they
provide, the candidate `Z` of §5.5, the credential extractor, the adversary
of the single-user setting, the simulation oracles of Remark 5.9, and the
theorem.

## The statement and the printed text

The statement differs from the printed text in seven points. Five make
explicit what the paper assumes or uses tacitly, points 1, 2, 3, 5 and 6.
Two depart from the printed statement, points 4 and 7, each at a gap the
paper itself records. `docs/DESIGN_ALTERNATIVES.md` records the decisions.

### 1. The unforgeability term is the advantage in the game with Help

**Printed.** The bound of Theorem 5.10 (p. 42) carries `Adv^ufcmva_μCMZ`.
Theorem 5.1 (p. 35) is proved for the game with the oracle `Help`, "we actually
will prove a stronger claim: the scheme is unforgeable even if the adversary is
given one additional oracle Help". The reduction `B` of the proof of Theorem
5.10 (p. 43) confirms the candidate `Z` through `Help`.

**Formalized.** The term is `UF_CMVAHelpAdv` of `UFCMVAHelp.lean`, the advantage
in the honest game of Figure 5 with the oracle `Help` answered by the key. The
paper ties `Help` to no model. The algebraic group model is a hypothesis of
Theorem 5.1 and Lemma 5.4 (pp. 35, 36) and of nothing in §5.5, so the theorem
puts no algebraic restriction on the single-user adversary of point 7. `microCMZ_ufcmva_le_of_wellBehaved` of `UFCMVA.lean` bounds the plain game
for well-behaved algebraic adversaries, whose translation (`AGMBridge.lean`)
answers `help` by `false`. A bound for the game with `Help` is open, issue
#235. That is where the model enters when the two theorems are chained.

### 2. The candidate `Z` is a function of the proof and the trace

**Printed.** "We are going to assume that the proof itself can provide a
candidate instance `Z`, and that the instance can be check for correctness
via the oracle Help" (p. 42). For Schnorr proofs the statement is recovered
"by looking at the trace of random oracle queries".

**Formalized.** `ZCandidate` is a function of the crs, the statement without
`Z`, the proof `π_p` and the random-oracle table, returning an optional group
element. `ZCandidateSound` is the assumption, that the function returns the
verifier's `Z` whenever `π_p` verifies on it from that table. The theorem takes
both as hypotheses. The instance fact for the Fiat–Shamir Σ-protocols belongs
to issue #3.

### 3. The extractor of Definition 4.5 takes the trace

**Printed.** Figure 8 (p. 31) writes `m := Ext.I(sk, φ, μ)` and
`m* := Ext.P(sk, φ*, ρ*)`. The proof of Theorem 5.10 defines both from the
extractors of the proof systems, which read the trace.

**Formalized.** `Extractor` of `Framework/Extractability.lean` receives the
random-oracle table as of the call and runs in `ProbComp`. `μCMZExtractor`
wraps the trace extractors of `ZKP_cmz.iu` and `ZKP_cmz.p`, with `Ext.P`
computing `Z` from the secret key as the server does, which is the check the
paper describes (p. 43, "internally, the extractor checks that `Z` was
correctly computed via the secret key").

### 4. The condition of Remark 5.9 is a hypothesis

**Printed.** The reduction `B` (p. 43) simulates `π_is` on every `Issue` query
and the knowledge-soundness adversaries built "from Items (i) and (ii)" extract
from `π_iu` and `π_p` produced after those simulated proofs. Remark 5.9 (p. 42)
names this case and says the gap closes with "different setup strings (or random
oracles)" per proof system, or for Schnorr proofs because "the vector sizes
mismatch". It gives no proof. The theorem has no hypothesis about it.

**Formalized.** `μCMZ_extractability` adds the condition as explicit arguments,
as `μCMZ_anonymity` does. `Piu`, `Pis` and `Pp` are three regions of the hash
domain. The setup, the prover and the verifier of each system are confined to
its region (`hiu`, `his`, `hp`). The simulator of `ZKP_cmz.is` is confined to
`Pis` (`hisSim`), and the extractors of `ZKP_cmz.iu` and `ZKP_cmz.p` to `Piu`
and `Pp` (`hiuExt`, `hpExt`). The regions are pairwise disjoint. The lemma
`ksndSimAdv_le_ksndAdv_of_domainSeparated` of `Core/NIZKP/Composition.lean` is
the Remark's assertion for one extraction. The simulation oracles
`risSimulationOracleIu` and `risSimulationOracleP` are the simulator of
`ZKP_cmz.is` with respect to each extracted system.

### 5. The crs is sampled in the §3.3 views

**Printed.** Definition 4.5 (p. 31) samples the crs inside the game, and so
do the §3.3 games.

**Formalized.** The views `riuNIZKPSampled`, `risNIZKPSampled` and
`rpNIZKPSampled` sample the crs as the credential's setup does, so every
advantage of the bound uses the same distribution of `H`. Theorem 5.8 fixes the
crs instead, since Definition 4.4 quantifies over it pointwise.

### 6. `gen ≠ 0`

**Printed.** Figure 9 (p. 34) takes `G` from the group description
`(𝔾, p, G) := Γ ← GrGen(1^λ)`, and the proof uses it as a generator tacitly.

**Formalized.** A hypothesis of the theorem, as in `μCMZ_anonymity`.

### 7. The single-user setting

**Printed.** Theorem 5.10 (p. 42) is stated for the game of Figure 8, which
has the oracles `NewUsr` and `PresentUsr`. §4.4 (p. 32) says "when proving
our keyed-verification credential systems, we do not consider the multi-user
setting", and the reduction `B` (p. 43) handles `Issue` and `Present` queries
only.

**Gap.** With `NewUsr` and `PresentUsr`, the statement fails for a proof system
whose proofs are malleable. A presentation of an honest user with a modified
proof lies outside `PQrs`, and its attributes lie outside `Qrs`.

**Formalized.** The theorem quantifies over `SUEXTAdversary`, an adversary
that never queries `NewUsr` or `PresentUsr`, embedded in `EXTGame` by
`SUEXTAdversary.toEXTAdversary`. The multi-user extension is step 8 of
item 13 of `docs/MICROCMZ_REMAINING.md`.

## The bound

The bound is the printed one, four terms and no query factors. The proof plan is
the one of §5.5. One hybrid replaces every `π_is` by a simulated one, charged to
zero knowledge of `ZKP_cmz.is`. A win by an `Issue` abort or by a presentation
the extractor cannot open is charged to knowledge soundness of `ZKP_cmz.iu` or
`ZKP_cmz.p`, under the condition of Remark 5.9. A win by a fresh extracted
attribute vector is a forgery of the reduction `B`. The reduction answers
`Issue` through the MAC code generation oracle and `Present` through the
candidate `Z`, `Help` and `Verify`, and outputs `(U', C_V − r'•H)`.

The four reductions are existential, as in `μCMZ_anonymity`. The development
fixes no efficiency notion on adversaries, so the inequality holds for
reductions of any cost. An unbounded `B` reaches advantage one in
`UF_CMVAHelpGame` by trying every scalar at `Verify`, so the inequality holds
for every adversary without the proof. Issue #240 tracks the efficiency notion
that makes it a security statement. The cryptographic content
of the statement is in the reductions its proof constructs. The proof phase may
replace the existential form by the explicit reductions, as
`agm_ufcmva_le_explicit` names its reductions.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework ENNReal

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (HS : HashSpec) (gen : G)

/-! ## The proof systems as §3.3 objects at the sampled crs

Per the reading of issue #176, the parameters `πiu n`, `πis` and `πp n` of the
credential are §3.3 proof systems for `R_cmz.iu`, `R_cmz.is` and `R_cmz.p`.
The views below sample the crs as the credential's setup does, point 5 of
the module docstring, where the views of `Anonymity.lean` fix it. -/

/-- `ZKP_cmz.iu` as a §3.3 proof system for `R_cmz.iu` (O24 Eq. 9), with the crs
sampled as the credential's setup samples it. -/
noncomputable def riuNIZKPSampled (n : ℕ) (π : RiuProofSystem HS G F n) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun secParam => liftM ((μCMZBaseMACSyntax F gen).setup secParam n))
    (fun _ x w => riuRel gen x w = true)

/-- `ZKP_cmz.is` as a §3.3 proof system for `R_cmz.is` (O24 Eq. 10), with the crs
sampled as the credential's setup samples it. -/
noncomputable def risNIZKPSampled (n : ℕ) (π : RisProofSystem HS G F) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun secParam => liftM ((μCMZBaseMACSyntax F gen).setup secParam n))
    (fun H' x w => risRel gen H' x w = true)

/-- `ZKP_cmz.p` as a §3.3 proof system for `R_cmz.p` (O24 Eq. 11), with the crs
sampled as the credential's setup samples it. -/
noncomputable def rpNIZKPSampled (n : ℕ) (π : RpProofSystem HS G F n) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun secParam => liftM ((μCMZBaseMACSyntax F gen).setup secParam n))
    (fun H' x w => rpRel gen H' x w = true)

/-- The relation of `riuNIZKPSampled` is decidable. -/
abbrev riuDecRelSampled (n : ℕ) (π : RiuProofSystem HS G F n) :
    (riuNIZKPSampled HS gen n π).DecidableRelation :=
  fun _ x w => show Decidable (riuRel gen x w = true) from inferInstance

/-- The relation of `risNIZKPSampled` is decidable. -/
abbrev risDecRelSampled (n : ℕ) (π : RisProofSystem HS G F) :
    (risNIZKPSampled HS gen n π).DecidableRelation :=
  fun H' x w => show Decidable (risRel gen H' x w = true) from inferInstance

/-- The relation of `rpNIZKPSampled` is decidable. -/
abbrev rpDecRelSampled (n : ℕ) (π : RpProofSystem HS G F n) :
    (rpNIZKPSampled HS gen n π).DecidableRelation :=
  fun H' x w => show Decidable (rpRel gen H' x w = true) from inferInstance

/-! ## The extractors and the simulator

The proof of Theorem 5.10 (§5.5, pp. 42 to 43) builds the credential
extractor from the extractors of `ZKP_cmz.iu` and `ZKP_cmz.p`, and its
reduction `B` simulates every `π_is` with the zero-knowledge simulator of
`ZKP_cmz.is`. The extractors are trace extractors, functions of the
statement, the proof and the oracle table, as in `Anonymity.lean`. -/

/-- The trace extractor of `ZKP_cmz.iu` at the crs `H : G`. -/
abbrev RiuExtractor {n : ℕ} (π : RiuProofSystem HS G F n) : Type :=
  G → RiuStmt G F n → π.Proof → HS.Cache → ProbComp (Option (RiuWitness F n))

/-- The trace extractor of `ZKP_cmz.p` at the crs `H : G`. -/
abbrev RpExtractor {n : ℕ} (π : RpProofSystem HS G F n) : Type :=
  G → RpStmt G F n → π.Proof → HS.Cache → ProbComp (Option (RpWitness F n))

/-- The zero-knowledge simulator of `ZKP_cmz.is` at the crs `H : G`. -/
abbrev RisSimulator (π : RisProofSystem HS G F) : Type :=
  G → RisStmt G → StateT HS.Cache ProbComp π.Proof

/-- A `RiuExtractor` as the `TraceExtractor` of `riuNIZKPSampled`. -/
def riuExtToTrace {n : ℕ} (π : RiuProofSystem HS G F n) (e : RiuExtractor HS π) :
    TraceExtractor HS (riuNIZKPSampled HS gen n π) :=
  fun {_} crs x pr c => e crs x pr c

/-- An `RpExtractor` as the `TraceExtractor` of `rpNIZKPSampled`. -/
def rpExtToTrace {n : ℕ} (π : RpProofSystem HS G F n) (e : RpExtractor HS π) :
    TraceExtractor HS (rpNIZKPSampled HS gen n π) :=
  fun {_} crs x pr c => e crs x pr c

/-- A `RisSimulator` as the `ZKSimulator` of `risNIZKPSampled`. -/
def risSimToZK (n : ℕ) (π : RisProofSystem HS G F) (s : RisSimulator HS π) :
    ZKSimulator HS (risNIZKPSampled HS gen n π) :=
  fun {_} crs x => s crs x

/-! ## The candidate `Z` of §5.5

The server recomputes `Z = (x₀ + xᵣ)•U' + Σᵢ xᵢ•Cᵢ − C_V` from the secret
key, which the reduction `B` does not hold. The paper assumes "that the proof
itself can provide a candidate instance `Z`" (p. 42), point 2 of the
module docstring. -/

/-- A candidate `Z` recovered from the crs, the statement of `R_cmz.p` without
`Z`, the proof `π_p` and the random-oracle table. -/
abbrev ZCandidate {n : ℕ} (π : RpProofSystem HS G F n) : Type :=
  G → G × PublicBases G n × (Fin n → G) × Policy F n → π.Proof → HS.Cache → Option G

/-- The assumption of §5.5 on a candidate `Z`. Whenever `π_p` verifies on the
statement `(U', X⃗, C⃗, Z, φ)` from a table, the candidate recovered from that
table is `Z`. -/
def ZCandidateSound {n : ℕ} (π : RpProofSystem HS G F n) (zc : ZCandidate HS π) : Prop :=
  ∀ (H U' : G) (X : PublicBases G n) (C : Fin n → G) (Z : G) (φ : Policy F n)
    (pr : π.Proof) (c c' : HS.Cache),
    (true, c') ∈ support (runRO HS c (π.verify H (U', X, C, Z, φ) pr)) →
    zc H (U', X, C, φ) pr c = some Z

variable (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
  (πp : ∀ n, RpProofSystem HS G F n)

/-! ## The credential extractor

`Ext.I(φ, (C', π_iu))` runs the extractor of `ZKP_cmz.iu` on the statement
`(C', X⃗, φ)` and returns the attributes `m⃗` of a witness `(m⃗, s)` that satisfies
`R_cmz.iu`. `Ext.P(φ*, (U', C_V, C⃗, π_p))` recomputes `Z` from the secret key
as the server does, runs the extractor of `ZKP_cmz.p` on
`(U', X⃗, C⃗, Z, φ*)` and returns the attributes `m⃗` of a witness `(r', r⃗, m⃗)`
that satisfies `R_cmz.p`. Both return `none` otherwise, the paper's abort
(pp. 42 to 43). -/

/-- The extractor `Ext = (Ext.I, Ext.P)` of the proof of O24 Theorem 5.10
(§5.5, pp. 42 to 43), over the trace extractors of `ZKP_cmz.iu` and
`ZKP_cmz.p`. -/
noncomputable def μCMZExtractor (extIu : ∀ n, RiuExtractor HS (πiu n))
    (extP : ∀ n, RpExtractor HS (πp n)) :
    Extractor HS (μCMZCredentialSyntax F HS gen πiu πis πp) where
  extI := fun {_ n} {H} c sk φ μ => do
    let (C', π) := μ
    let stmt : RiuStmt G F n := (C', credBases gen sk, φ)
    match ← extIu n H stmt π c with
    | some w => if riuRel gen stmt w then pure (some w.1) else pure none
    | none => pure none
  extP := fun {_ n} {H} c sk φ ρ => do
    let (U', CV, C, π) := ρ
    let Z := (sk.1 + sk.2.1) • U' + (∑ i, sk.2.2 i • C i) - CV
    let stmt : RpStmt G F n := (U', credBases gen sk, C, Z, φ)
    match ← extP n H stmt π c with
    | some w => if rpRel gen H stmt w then pure (some w.2.2) else pure none
    | none => pure none

/-! ## The single-user setting

§4.4 (p. 32) says "when proving our keyed-verification credential systems, we do
not consider the multi-user setting", and the reduction of Theorem 5.10 (p. 43)
handles `Issue` and `Present` queries only. The statement is therefore for an
adversary of the single-user setting, which queries `Issue`, `Present` and the
random oracle and never `NewUsr` or `PresentUsr`, point 7 of the module
docstring. `SUEXTAdversary.toEXTAdversary` embeds its queries in `EXTGame`.
Without the restriction the statement fails for a proof system whose proofs are
malleable. A presentation of an honest user with a modified proof verifies, lies
outside `PQrs`, and its attributes lie outside `Qrs`, which Figure 8 fills from
`Issue` only. The adversary therefore wins whether or not the extractor opens
it. §4.4 (p. 32) notes that the condition `(φ*, ρ*) ∉ PQrs` is what strong
simulation extractability covers. The multi-user extension is step 8 of item 13
of `docs/MICROCMZ_REMAINING.md`. -/

/-- The oracle calls of the single-user setting, the `issue` and `present` arms
of `EXTQuery` at the credential of Figure 9. -/
inductive SUEXTQuery (n : ℕ) : Type where
  /-- `Issue(φ, μ)`, the server's issuance response. -/
  | issue : Policy F n → G × (πiu n).Proof → SUEXTQuery n
  /-- `Present(φ, ρ)`, the server's presentation check. -/
  | present : Policy F n → G × G × (Fin n → G) × (πp n).Proof → SUEXTQuery n

/-- Answer types of `SUEXTQuery`, those of `EXTOracleSpec`. -/
def SUEXTOracleSpec (n : ℕ) : OracleSpec (SUEXTQuery HS πiu πp n)
  | .issue _ _ => Option (G × G × πis.Proof)
  | .present _ _ => Bool

/-- The oracle interface of a single-user extraction adversary, the two oracles
and the random oracle. -/
abbrev SUEXTAdvSpec (n : ℕ) : OracleSpec (SUEXTQuery HS πiu πp n ⊕ (ℕ ⊕ HS.Dom)) :=
  SUEXTOracleSpec HS πiu πis πp n + ZKRO HS

/-- An extraction adversary of the single-user setting. Given the crs `H` and
the public parameters, it queries `Issue`, `Present` and the random oracle, and
outputs the challenge `(φ*, ρ*)`. -/
structure SUEXTAdversary where
  /-- The adversary's program, from the crs and the public parameters. -/
  run : {n : ℕ} → G → Params G n →
    OracleComp (SUEXTAdvSpec HS πiu πis πp n)
      (Policy F n × (G × G × (Fin n → G) × (πp n).Proof))

/-- The queries of the single-user setting as queries of `EXTGame`. -/
def suQueryImpl {secParam n : ℕ} (H : G) :
    QueryImpl (SUEXTAdvSpec HS πiu πis πp n)
      (OracleComp (EXTAdvSpec HS (μCMZCredentialSyntax F HS gen πiu πis πp)
        (secParam := secParam) (n := n) H))
  | .inl (.issue φ μ) =>
      query (spec := EXTAdvSpec HS (μCMZCredentialSyntax F HS gen πiu πis πp)
          (secParam := secParam) (n := n) H)
        (.inl (.issue φ μ))
  | .inl (.present φ ρ) =>
      query (spec := EXTAdvSpec HS (μCMZCredentialSyntax F HS gen πiu πis πp)
          (secParam := secParam) (n := n) H)
        (.inl (.present φ ρ))
  | .inr t => query (spec := EXTAdvSpec HS (μCMZCredentialSyntax F HS gen πiu πis πp)
          (secParam := secParam) (n := n) H) (.inr t)

/-- A single-user adversary as an adversary of `EXTGame`, its queries embedded
through `suQueryImpl`. It never queries `NewUsr` or `PresentUsr`. -/
def SUEXTAdversary.toEXTAdversary (A : SUEXTAdversary HS πiu πis πp) :
    EXTAdversary HS (μCMZCredentialSyntax F HS gen πiu πis πp) where
  run := fun {secParam n} H pp =>
    simulateQ (suQueryImpl HS gen πiu πis πp (secParam := secParam) (n := n) H)
      (A.run (n := n) H pp)

/-! ## The simulation oracles of Remark 5.9

The knowledge-soundness adversaries of the proof extract from `π_iu` and `π_p`
that the credential adversary produced after receiving simulated proofs `π_is`.
That is knowledge soundness of `ZKP_cmz.iu` and of `ZKP_cmz.p` with a simulation
oracle for `ZKP_cmz.is`, the game `ksndSimGame` of `Core/NIZKP/Composition`. The
lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated` bounds it by the printed term
under the hypotheses of point 4. -/

/-- The simulator of `ZKP_cmz.is` as the simulation oracle with respect to
`ZKP_cmz.iu`. -/
noncomputable def risSimulationOracleIu (n : ℕ) (simIs : RisSimulator HS πis) :
    SimulationOracle HS (riuNIZKPSampled HS gen n (πiu n)) where
  Query := fun _ => RisStmt G
  spec := fun _ _ => πis.Proof
  impl := fun H' x => simIs H' x

/-- The simulator of `ZKP_cmz.is` as the simulation oracle with respect to
`ZKP_cmz.p`. -/
noncomputable def risSimulationOracleP (n : ℕ) (simIs : RisSimulator HS πis) :
    SimulationOracle HS (rpNIZKPSampled HS gen n (πp n)) where
  Query := fun _ => RisStmt G
  spec := fun _ _ => πis.Proof
  impl := fun H' x => simIs H' x

/-! ## Theorem 5.10

The bound is the printed one. The hypotheses are points 2, 4, 6 and 7 of
the module docstring. -/

/-- **O24 Theorem 5.10.** For `gen ≠ 0`, the extraction advantage of an
adversary of the single-user setting with respect to `μCMZExtractor` is at most
the unforgeability advantage of μCMZ in the game with `Help` plus the
zero-knowledge advantage of `ZKP_cmz.is` and the knowledge-soundness advantages
of `ZKP_cmz.iu` and `ZKP_cmz.p`. The reductions `B`, `A'`, `A''` and `A'''` are
existential and carry no cost bound, see the module docstring. The hypotheses
`hzc` and `hiu` to `hpExt` are the assumption on the candidate `Z` and the
condition of Remark 5.9. The proof is deferred. -/
theorem μCMZ_extractability (simIs : RisSimulator HS πis)
    (extIu : ∀ n, RiuExtractor HS (πiu n)) (extP : ∀ n, RpExtractor HS (πp n))
    (hgen : gen ≠ 0) {secParam n : ℕ}
    (zc : ZCandidate HS (πp n)) (hzc : ZCandidateSound HS (πp n) zc)
    (A : SUEXTAdversary HS πiu πis πp)
    (Piu Pis Pp : Region HS)
    (hiu : ConfinedSystem HS (riuNIZKPSampled HS gen n (πiu n)) Piu)
    (hiuExt : TraceExtractor.ConfinedTo (riuExtToTrace HS gen (πiu n) (extIu n)) Piu)
    (his : ConfinedSystem HS (risNIZKPSampled HS gen n πis) Pis)
    (hisSim : ZKSimulatorConfinedTo (risSimToZK HS gen n πis simIs) Pis)
    (hp : ConfinedSystem HS (rpNIZKPSampled HS gen n (πp n)) Pp)
    (hpExt : TraceExtractor.ConfinedTo (rpExtToTrace HS gen (πp n) (extP n)) Pp)
    (hiu_is : Piu.Disjoint Pis) (hiu_p : Piu.Disjoint Pp) (his_p : Pis.Disjoint Pp) :
    ∃ (B : UFHelpAdversary F G n)
      (A' : ZKAdversary HS (risNIZKPSampled HS gen n πis))
      (A'' : KSNDAdversary HS (riuNIZKPSampled HS gen n (πiu n)))
      (A''' : KSNDAdversary HS (rpNIZKPSampled HS gen n (πp n))),
      EXTAdv HS (μCMZCredentialSyntax F HS gen πiu πis πp)
          (μCMZExtractor HS gen πiu πis πp extIu extP)
          (SUEXTAdversary.toEXTAdversary HS gen πiu πis πp A) secParam n ≤
        UF_CMVAHelpAdv gen B secParam
        + ENNReal.ofReal (ZKAdv HS (risNIZKPSampled HS gen n πis) (risDecRelSampled HS gen n πis)
            A' (risSimToZK HS gen n πis simIs) secParam)
        + KSNDAdv HS (riuNIZKPSampled HS gen n (πiu n))
            (TraceExtractor.toKSND (riuExtToTrace HS gen (πiu n) (extIu n))) A''
            (riuDecRelSampled HS gen n (πiu n)) secParam
        + KSNDAdv HS (rpNIZKPSampled HS gen n (πp n))
            (TraceExtractor.toKSND (rpExtToTrace HS gen (πp n) (extP n))) A'''
            (rpDecRelSampled HS gen n (πp n)) secParam := by
  sorry

end KVAC.Schemes.MicroCMZ
