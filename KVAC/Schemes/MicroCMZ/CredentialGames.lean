/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Credential
import KVAC.Framework.Extractability
import KVAC.Framework.Anonymity

/-!
# The security games at the μCMZ credential

The extraction game `EXTGame` of Figure 8 and the anonymity game of Definition 4.4 elaborate at
the μCMZ instance `μCMZCredentialSyntax` of Figure 9. This file holds only `example`s and declares
nothing. The Theorem 5.8 and Theorem 5.10 statements write `AnonAdv HS (μCMZCredentialSyntax …)`
and `EXTAdv HS (μCMZCredentialSyntax …)` directly, as the review note of issue #163 asks, so no
local advantage is defined here. The statement files, their extractor and their simulator belong to
issues #10 and #179.

## What the games ask of the scheme

- `DecidableEq (MsgVec crs)`, for the check `m* ∉ Qrs` of `EXTGame`. The instance supplies it
  through `DecidableEqMsg`, from `DecidableEq F`.
- `DecidableEq (Pred crs)`, for the check `(φ*, ρ*) ∉ PQrs`. The instance supplies it through
  `DecidableEqPred`, from `Fintype F` and `DecidableEq F`.
- `DecidableEq (PresentMsg crs)`, for the same check. The instance supplies it through
  `DecidableEqPresentMsg`, from `DecidableEq G` and the field `DecidableEqProof`.
- `exactPred` and `holds_exactPred`, for the `NewUsr` oracle. The instance supplies
  `exactPolicy` and `exactPolicy_eq_true_iff`.
- `NonemptyMsg`, for `Anonymous` and `AnonymousPoly` only. The scalar `0 : F` witnesses it.

Every hypothesis is a field of `KVACSyntax` or of `ProofSystemFor`, or follows from the section
variables of `Credential.lean`. The anonymity advantage `AnonAdv` needs no decidability beyond
`holds`, which returns `Bool`.

## Elaboration notes for the statements

- The crs of the instance is `H : G`, whose type mentions neither the security parameter nor the
  attribute count. A crs argument therefore fixes neither, and `EXTAdvSpec`, `AnonAdv` and the
  carriers take `secParam` and `n` as named arguments.
- The instance is `noncomputable`, so every example that mentions it is too.
- `NonemptyMsg` takes the witness `(0 : F)` with its type. The bare numeral `0` at the carrier
  `Msg crs` makes the elaborator search for an `OfNat` instance at an unreduced type, and the
  check did not finish within 300 seconds.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework ENNReal

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (HS : HashSpec) (gen : G)
  (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
  (πp : ∀ n, RpProofSystem HS G F n)

/-! ## Extractability -/

/-- The extraction advantage at the instance, for any extractor and any adversary. -/
noncomputable example (ext : Extractor (μCMZCredentialSyntax F HS gen πiu πis πp))
    (A : EXTAdversary HS (μCMZCredentialSyntax F HS gen πiu πis πp)) (secParam n : ℕ) :
    ℝ≥0∞ :=
  EXTAdv HS (μCMZCredentialSyntax F HS gen πiu πis πp) ext A secParam n

/-- An extractor of the instance from components typed over the Figure 9 carriers. The key is
`Key F n`, the predicate `Policy F n`, the issuance message `(C', π_iu)`, the presentation
message `(U', C_V, C⃗, π_p)` and the attribute vector `Fin n → F`. The carriers unfold by
definition. -/
example
    (extI : ∀ {n : ℕ}, Key F n → Policy F n → G × (πiu n).Proof → Option (Fin n → F))
    (extP : ∀ {n : ℕ}, Key F n → Policy F n → G × G × (Fin n → G) × (πp n).Proof →
      Option (Fin n → F)) :
    Extractor (μCMZCredentialSyntax F HS gen πiu πis πp) :=
  ⟨fun sk φ μ => extI sk φ μ, fun sk φ ρ => extP sk φ ρ⟩

/-- The challenge `(φ*, ρ*)` of an extraction adversary at the instance, a policy and a
presentation message `(U', C_V, C⃗, π_p)`. -/
example (A : EXTAdversary HS (μCMZCredentialSyntax F HS gen πiu πis πp))
    {secParam n : ℕ} (crs : G) (pp : Params G n) :
    OracleComp (EXTAdvSpec HS (μCMZCredentialSyntax F HS gen πiu πis πp)
        (secParam := secParam) (n := n) crs)
      (Policy F n × (G × G × (Fin n → G) × (πp n).Proof)) :=
  A.run crs pp

/-- The decidable equality that the check `(φ*, ρ*) ∉ PQrs` of `EXTGame` resolves. -/
noncomputable example {secParam n : ℕ} (crs : G) :
    DecidableEq
      ((μCMZCredentialSyntax F HS gen πiu πis πp).Pred (secParam := secParam) (n := n) crs ×
        (μCMZCredentialSyntax F HS gen πiu πis πp).PresentMsg (secParam := secParam) (n := n)
          crs) :=
  inferInstance

/-- The decidable equality that the check `m* ∉ Qrs` of `EXTGame` resolves. -/
noncomputable example {secParam n : ℕ} (crs : G) :
    DecidableEq
      ((μCMZCredentialSyntax F HS gen πiu πis πp).MsgVec (secParam := secParam) (n := n) crs) :=
  inferInstance

/-! ## Anonymity -/

/-- The anonymity advantage at the instance, at a fixed crs `H : G`, key `sk : Key F n`, public
parameters `pp : Params G n`, attribute vector, policy and random-oracle table. -/
noncomputable example (issuer : AnonIssuer HS (μCMZCredentialSyntax F HS gen πiu πis πp))
    (D : AnonDistinguisher HS (μCMZCredentialSyntax F HS gen πiu πis πp) issuer.StA)
    (sim : AnonSimulator HS (μCMZCredentialSyntax F HS gen πiu πis πp))
    {secParam n : ℕ} (crs : G) (sk : Key F n) (pp : Params G n) (m : Fin n → F)
    (φ : Policy F n) (cache₀ : HS.spec.QueryCache) : ℝ :=
  AnonAdv HS (μCMZCredentialSyntax F HS gen πiu πis πp) issuer D sim
    (secParam := secParam) (n := n) crs sk pp m φ cache₀

/-- The message family of the instance is non-empty, the standing assumption of `Anonymous`. -/
example : NonemptyMsg (μCMZCredentialSyntax F HS gen πiu πis πp) :=
  fun _ => ⟨(0 : F)⟩

end KVAC.Schemes.MicroCMZ
