/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Credential
import KVAC.Core.NIZKP.Composition

/-!
# Anonymity of μCMZ (O24 §5.4, Theorem 5.8)

Toward the statement of O24 Theorem 5.8 for `μCMZCredentialSyntax` of
Figure 9. This part adds the zero-knowledge simulators and the extractor of
the three proof systems. The simulation oracle of Remark 5.9, the simulator of
the proof and the theorem follow in later parts.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework ENNReal

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (HS : HashSpec) (gen : G)

/-! ## The proof systems as §3.3 objects

Per the reading of issue #176, the parameters `πiu n`, `πis` and `πp n` of the
credential are §3.3 proof systems for `R_cmz.iu`, `R_cmz.is` and `R_cmz.p`.
`riuNIZKP`, `risNIZKP` and `rpNIZKP` are those views, with the crs fixed at the
`H` of the statement. Definition 4.4 quantifies over the crs pointwise and the
§3.3 games sample it, and the fixed crs is the bridge between the two
(`docs/DESIGN_ALTERNATIVES.md`). -/

/-- `ZKP_cmz.iu` as a §3.3 proof system at the crs `H` for `R_cmz.iu` (O24 Eq. 9). -/
noncomputable def riuNIZKP {n : ℕ} (H : G) (π : RiuProofSystem HS G F n) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun _ => pure H) (fun _ x w => riuRel gen x w = true)

/-- `ZKP_cmz.is` as a §3.3 proof system at the crs `H` for `R_cmz.is` (O24 Eq. 10). -/
noncomputable def risNIZKP (H : G) (π : RisProofSystem HS G F) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun _ => pure H) (fun H' x w => risRel gen H' x w = true)

/-- `ZKP_cmz.p` as a §3.3 proof system at the crs `H` for `R_cmz.p` (O24 Eq. 11). -/
noncomputable def rpNIZKP {n : ℕ} (H : G) (π : RpProofSystem HS G F n) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun _ => pure H) (fun H' x w => rpRel gen H' x w = true)

/-- The relation of `riuNIZKP` is decidable. -/
abbrev riuDecRel {n : ℕ} (H : G) (π : RiuProofSystem HS G F n) :
    (riuNIZKP HS gen H π).DecidableRelation :=
  fun _ x w => show Decidable (riuRel gen x w = true) from inferInstance

/-- The relation of `risNIZKP` is decidable. -/
abbrev risDecRel (H : G) (π : RisProofSystem HS G F) :
    (risNIZKP HS gen H π).DecidableRelation :=
  fun H' x w => show Decidable (risRel gen H' x w = true) from inferInstance

/-- The relation of `rpNIZKP` is decidable. -/
abbrev rpDecRel {n : ℕ} (H : G) (π : RpProofSystem HS G F n) :
    (rpNIZKP HS gen H π).DecidableRelation :=
  fun H' x w => show Decidable (rpRel gen H' x w = true) from inferInstance

/-! ## The simulators and the extractor

Definition 4.4 asks for an algorithm that plays the user without the attributes
`m`. The proof of Theorem 5.8 (§5.4, p. 40) builds it from three objects that
the proof systems provide. The zero-knowledge simulator of `ZKP_cmz.iu`
produces `π_iu` from the statement `(C', X, φ)` alone. The extractor of
`ZKP_cmz.is` recovers the witness `(x₀, u)` of the issuer's proof `π_is`. The
zero-knowledge simulator of `ZKP_cmz.p` produces `π_p` from the statement
`(U', X, C, Z, φ')` alone.

The extractor is a `TraceExtractor`, a function of the statement, the proof and
the oracle table, departure 1 of the module docstring. -/

/-- The zero-knowledge simulator of `ZKP_cmz.iu` at the crs `H : G`. -/
abbrev RiuSimulator {n : ℕ} (π : RiuProofSystem HS G F n) : Type :=
  G → RiuStmt G F n → StateT HS.Cache ProbComp π.Proof

/-- The zero-knowledge simulator of `ZKP_cmz.p` at the crs `H : G`. -/
abbrev RpSimulator {n : ℕ} (π : RpProofSystem HS G F n) : Type :=
  G → RpStmt G F n → StateT HS.Cache ProbComp π.Proof

/-- The trace extractor of `ZKP_cmz.is` at the crs `H : G`. -/
abbrev RisExtractor (π : RisProofSystem HS G F) : Type :=
  G → RisStmt G → π.Proof → HS.Cache → ProbComp (Option (RisWitness F))

/-- A `RiuSimulator` as the `ZKSimulator` of `riuNIZKP`. -/
def riuSimToZK {n : ℕ} (H : G) (π : RiuProofSystem HS G F n) (s : RiuSimulator HS π) :
    ZKSimulator HS (riuNIZKP HS gen H π) :=
  fun {_} crs x => s crs x

/-- An `RpSimulator` as the `ZKSimulator` of `rpNIZKP`. -/
def rpSimToZK {n : ℕ} (H : G) (π : RpProofSystem HS G F n) (s : RpSimulator HS π) :
    ZKSimulator HS (rpNIZKP HS gen H π) :=
  fun {_} crs x => s crs x

/-- A `RisExtractor` as the `TraceExtractor` of `risNIZKP`. -/
def risExtToTrace (H : G) (π : RisProofSystem HS G F) (e : RisExtractor HS π) :
    TraceExtractor HS (risNIZKP HS gen H π) :=
  fun {_} crs x pr c => e crs x pr c

end KVAC.Schemes.MicroCMZ
