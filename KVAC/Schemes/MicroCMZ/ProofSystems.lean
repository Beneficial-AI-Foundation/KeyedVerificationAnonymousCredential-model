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

`ProofSystemFor M Crs Stmt Witness` is the prover and verifier of an
`NIZKPSyntax` with the crs, statement and witness types fixed, so the issuance
and presentation moves can build statements. Both algorithms take the crs,
because R_is and R_p mention the crs element `H` (O24 Figure 9, `X₀ = x₀·H` and
`Z = Σᵢ rᵢ·Xᵢ − r'·H`), which the credential's `setup` samples. The structure
carries no relation. `ProofSystemFor.toNIZKPSyntax` supplies one, together with
a setup, so the §3.3 properties apply. The hypothesis of issue #176 that the
three systems prove R_cmz constrains them through it.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core

/-- A non-interactive proof system for fixed crs, statement and witness types,
with the computations in `M`. Decidable equality on proofs is a field, since
the presentation message carries π_p and the extraction game compares
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

/-- The proof system π_iu of the user's issuance proof, for R_iu (O24 Eq. 9),
with the crs element `H : G`. -/
abbrev RiuProofSystem (HS : HashSpec) (G F : Type) (n : ℕ) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO HS)) G (RiuStmt G F n) (RiuWitness F n)

/-- The proof system π_is of the server's issuance proof, for R_is (O24 Eq. 10),
with the crs element `H : G`. -/
abbrev RisProofSystem (HS : HashSpec) (G F : Type) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO HS)) G (RisStmt G) (RisWitness F)

/-- The proof system π_p of the presentation proof, for R_p (O24 Eq. 11), with
the crs element `H : G`. -/
abbrev RpProofSystem (HS : HashSpec) (G F : Type) (n : ℕ) : Type 1 :=
  ProofSystemFor (OracleComp (ZKRO HS)) G (RpStmt G F n) (RpWitness F n)

end KVAC.Schemes.MicroCMZ
