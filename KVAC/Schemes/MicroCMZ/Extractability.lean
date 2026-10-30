/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Credential
import KVAC.Framework.Extractability

/-!
# Extractability of μCMZ (O24 §5.5, Theorem 5.10)

The setting of O24 Theorem 5.10 for `μCMZCredentialSyntax` of Figure 9. The
sections below hold, in order, the three proof systems as §3.3 objects at the
sampled crs, the extractor and simulator types, the candidate `Z` of §5.5, and
the adversary of the single-user setting. The credential extractor, the
simulation oracles of Remark 5.9 and the theorem follow in the Theorem 5.10
statement of #179.

## The statement and the printed text

The objects of this file differ from the printed text in three points, numbered
as in the Theorem 5.10 statement of #179, which adds the other four. Points 2
and 5 make explicit what the paper assumes tacitly. Point 7 departs from the
printed statement at a gap the paper itself records.
`docs/DESIGN_ALTERNATIVES.md` records the decisions.

### 2. The candidate `Z` is a function of the proof and the trace

**Printed.** "We are going to assume that the proof itself can provide a
candidate instance `Z`, and that the instance can be check for correctness
via the oracle Help" (p. 42). For Schnorr proofs the statement is recovered
"by looking at the trace of random oracle queries".

**Formalized.** `ZCandidate` is a function of the crs, the statement without
`Z`, the proof `π_p` and the random-oracle table, returning an optional group
element. `ZCandidateSound` is the assumption, that the function returns the
verifier's `Z` whenever `π_p` verifies on it from that table. The Theorem 5.10
statement of #179 takes both as hypotheses. The instance fact for the
Fiat–Shamir Σ-protocols belongs to issue #3.

### 5. The crs is sampled in the §3.3 views

**Printed.** Definition 4.5 (p. 31) samples the crs inside the game, and so
do the §3.3 games.

**Formalized.** The views `riuNIZKPSampled`, `risNIZKPSampled` and
`rpNIZKPSampled` sample the crs as the credential's setup does, so every
advantage of the bound uses the same distribution of `H`. Theorem 5.8 fixes the
crs instead, since Definition 4.4 quantifies over it pointwise.

### 7. The single-user setting

**Printed.** Theorem 5.10 (p. 42) is stated for the game of Figure 8, which
has the oracles `NewUsr` and `PresentUsr`. §4.4 (p. 32) says "when proving
our keyed-verification credential systems, we do not consider the multi-user
setting", and the reduction `B` (p. 43) handles `Issue` and `Present` queries
only.

**Gap.** With `NewUsr` and `PresentUsr`, the statement fails for a proof system
whose proofs are malleable. A presentation of an honest user with a modified
proof lies outside `PQrs`, and its attributes lie outside `Qrs`.

**Formalized.** The Theorem 5.10 statement of #179 quantifies over
`SUEXTAdversary`, an adversary that never queries `NewUsr` or `PresentUsr`,
embedded in `EXTGame` by `SUEXTAdversary.toEXTAdversary`. The multi-user
extension is step 8 of item 13 of `docs/MICROCMZ_REMAINING.md`.

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

end KVAC.Schemes.MicroCMZ
