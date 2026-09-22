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
Credentials*, IACR ePrint 2024/1552 (O24), attaches three non-interactive
proofs π_iu, π_is and π_p for the relations R_iu, R_is and R_p of
`KVAC.Schemes.MicroCMZ.Relations`. The credential instance takes the three
proof systems as parameters rather than fixing a Fiat–Shamir compilation.

`ProofSystemFor M Stmt Witness` is the prover and verifier of an `NIZKPSyntax`
with the statement and witness types fixed, so the issuance and presentation
moves can build statements. It has no `setup` and no crs, because the
credential crs `H` and the shared random oracle `ZKRO H` already play that
role. It carries no relation either. The hypothesis of issue #176 that the
three systems prove R_cmz constrains them separately.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core

/-- A non-interactive proof system for fixed statement and witness types, with
the computations in `M`. Decidable equality on proofs is a field, since the
presentation message carries π_p and the games compare messages. -/
structure ProofSystemFor (M : Type → Type) (Stmt Witness : Type) where
  /-- The proof type. -/
  Proof : Type
  /-- Decidable equality on proofs. -/
  DecidableEqProof : DecidableEq Proof
  /-- The prover, from a statement and a witness. -/
  prove : Stmt → Witness → M Proof
  /-- The verifier, monadic because a Fiat–Shamir verifier queries the
  random oracle. -/
  verify : Stmt → Proof → M Bool

namespace ProofSystemFor

/-- `DecidableEqProof` promoted to an instance. -/
instance {M : Type → Type} {Stmt Witness : Type} (π : ProofSystemFor M Stmt Witness) :
    DecidableEq π.Proof :=
  π.DecidableEqProof

end ProofSystemFor

/-- The proof system π_iu of the user's issuance proof, for R_iu (O24 Eq. 9). -/
abbrev RiuProofSystem (H : HashSpec) (G F : Type) (n : ℕ) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO H)) (RiuStmt G F n) (RiuWitness F n)

/-- The proof system π_is of the server's issuance proof, for R_is (O24 Eq. 10). -/
abbrev RisProofSystem (H : HashSpec) (G F : Type) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO H)) (RisStmt G) (RisWitness F)

/-- The proof system π_p of the presentation proof, for R_p (O24 Eq. 11). -/
abbrev RpProofSystem (H : HashSpec) (G F : Type) (n : ℕ) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO H)) (RpStmt G F n) (RpWitness F n)

end KVAC.Schemes.MicroCMZ
