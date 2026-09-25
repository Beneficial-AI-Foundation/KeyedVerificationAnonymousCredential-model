/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Relations
import KVAC.Core.NIZKP.Security

/-!
# Proof-system parameters of the μCMZ credential (O24 §5.1, Figure 9)

The μCMZ credential of Orrù, *Revisiting Keyed-Verification Anonymous
Credentials*, IACR ePrint 2024/1552 (O24), uses three non-interactive proof
systems `ZKP_cmz.iu`, `ZKP_cmz.is` and `ZKP_cmz.p` for the relations
`R_cmz.iu`, `R_cmz.is` and `R_cmz.p` of O24 Eqs. 9 to 11, formalized in
`KVAC.Schemes.MicroCMZ.Relations`. They produce the proofs `π_iu`, `π_is` and
`π_p` of O24 Figure 9. O24 leaves them abstract, assuming a proof system for a
relation `R ⊇ R_cmz`, where `R_cmz = R_cmz.iu ∪ R_cmz.is ∪ R_cmz.p` (O24
Theorem 5.2). The credential instance of A3 takes the three proof systems as
arguments, so it does not depend on a particular construction such as the
Fiat–Shamir compilation of the Σ-protocols in `Relations.lean`.

## Role

`ProofSystemFor` is the bridge between the μCMZ credential (O24 Figure 9) and
the abstract proof systems of O24 §3.3 (`KVAC.Core.NIZKP`). The credential side
sees a proof system for one of the relations `R_cmz.*`, with prove and verify
algorithms it calls on the statements it builds. The §3.3 side sees an
`NIZKPSyntax`, the object over which `KVAC.Core.NIZKP` states completeness,
zero-knowledge and knowledge soundness. `ProofSystemFor.toNIZKPSyntax` maps
the first view to the second, so the security statements about μCMZ can
assume the §3.3 properties of the very proof systems its algorithms call.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core

/-- A non-interactive proof system for fixed crs, statement and witness types,
with the computations in `M`. Decidable equality on proofs is a field, since
the presentation message carries the proof `π_p` and the extraction game compares
presentation messages. -/
structure ProofSystemFor (M : Type → Type) (Crs Stmt Witness : Type) where
  /-- The proof type. -/
  Proof : Type
  /-- Decidable equality on proofs. -/
  DecidableEqProof : DecidableEq Proof
  /-- The prover, from the crs, a statement and a witness. -/
  prove : Crs → Stmt → Witness → M Proof
  /-- The verifier, monadic because a Fiat–Shamir verifier queries the
  random oracle. -/
  verify : Crs → Stmt → Proof → M Bool

namespace ProofSystemFor

/-- `DecidableEqProof` promoted to an instance. -/
instance {M : Type → Type} {Crs Stmt Witness : Type}
    (π : ProofSystemFor M Crs Stmt Witness) : DecidableEq π.Proof :=
  π.DecidableEqProof

/-- The `NIZKPSyntax` of `π` with the setup `setup` and the crs-indexed relation
`rel`. The §3.3 properties (`PerfectlyComplete`, `zkGameReal`, `ksndGame`,
`seGame`) take an `NIZKPSyntax (OracleComp (ZKRO H))`, so they apply to `π` at
that carrier through this definition. -/
def toNIZKPSyntax {M : Type → Type} [Monad M] {Crs Stmt Witness : Type}
    (π : ProofSystemFor M Crs Stmt Witness) (setup : ℕ → M Crs)
    (rel : Crs → Stmt → Witness → Prop) : NIZKPSyntax M where
  Crs _ := Crs
  Stmt _ := Stmt
  Witness _ := Witness
  Proof _ := π.Proof
  setup := setup
  prove := π.prove
  verify := π.verify
  relation := rel

end ProofSystemFor

/-- The type of `ZKP_cmz.iu`, the proof system of the user's issuance proof
`π_iu`, for `R_cmz.iu` (O24 Eq. 9), with the crs element `H : G`. -/
abbrev RiuProofSystem (HS : HashSpec) (G F : Type) (n : ℕ) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO HS)) G (RiuStmt G F n) (RiuWitness F n)

/-- The type of `ZKP_cmz.is`, the proof system of the server's issuance proof
`π_is`, for `R_cmz.is` (O24 Eq. 10), with the crs element `H : G`. -/
abbrev RisProofSystem (HS : HashSpec) (G F : Type) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO HS)) G (RisStmt G) (RisWitness F)

/-- The type of `ZKP_cmz.p`, the proof system of the presentation proof `π_p`,
for `R_cmz.p` (O24 Eq. 11), with the crs element `H : G`. -/
abbrev RpProofSystem (HS : HashSpec) (G F : Type) (n : ℕ) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO HS)) G (RpStmt G F n) (RpWitness F n)

end KVAC.Schemes.MicroCMZ
