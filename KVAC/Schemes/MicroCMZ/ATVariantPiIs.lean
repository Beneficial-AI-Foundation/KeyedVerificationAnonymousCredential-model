/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.ATVariant
import KVAC.Schemes.MicroCMZ.CredentialCorrectness
import KVAC.Preliminaries.AnonymousTokens.OracleCarrier

/-!
# μCMZ_AT with the issuer's proof `π_is` (O24 §5.2, Figure 9)

The anonymous-token variant `μCMZ_AT` of O24 Figure 9: the boxed user proof
`π_iu` removed, the issuer's proof `π_is` kept, as an `ATSyntax` at the oracle
carrier `OracleComp (ZKRO HS)`, with the proof system `ZKP_cmz.is` a parameter.
The core of `ATVariant.lean` removes both proofs; the scheme of this file is the
one the paper's Theorems 5.3 and 5.11 name. Its one-more unforgeability game is
`OMUFGameRO` (`KVAC.Preliminaries.AnonymousTokens.OracleCarrier`), whose
random-oracle cache the server's proofs share with the adversary. Both issuance
nonces `u` and `r` are drawn nonzero, as in the core (*Nonzero sampling* in
`ATVariant.lean`).

## Reuse

Setup, key generation and the key and message types are those of the μCMZ
credential, `μCMZCredKeyedSetup`: the base MAC's setup and key generation lifted
through `liftM`. The user's first move, `atIssueUsr₁PiIs`, is the core's
`atIssueUsr₁` lifted, keeping the public parameters in the state for the second
move, which is the credential's `credIssueUsr₂`: check `U' ≠ 0`, verify `π_is` on
`(X₀, C' + Xᵣ, U', V')`, and unblind. The server is the credential's
`credIssueSrv` without the `π_iu` check. Verification is the base MAC's `verify`,
as for the core.

## Correctness

`μCMZAT_correctRO` proves `ATSyntax.CorrectRO` under a nonzero generator and the
perfect completeness of `π_is` for `R_cmz.is`, in the form
`ProofSystemFor.CompleteRO` of the credential's correctness, with the crs setup
`H ←$ G×`.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Preliminaries

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

variable (HS : HashSpec)

/-- Issuance, server's move of `μCMZ_AT` (O24 Figure 9, `π_iu` removed): sample
`u ←$ F×` (nonzero, where the paper writes `u ←$ ℤ_p`; see *Nonzero sampling*
in `ATVariant.lean`) and answer `U' = u·G`, `V' = x₀·U' + u·(C' + Xᵣ)` with the
proof `π_is` for `(X₀, C' + Xᵣ, U', V')` and witness `(x₀, u)`. The credential's
`credIssueSrv` without the `π_iu` check. -/
noncomputable def atIssueSrvPiIs {n : ℕ} (gen H : G) (πis : RisProofSystem HS G F)
    (sk : Key F n) (C' : G) : OracleComp (ZKRO HS) (Option (G × G × πis.Proof)) := do
  let u ← liftM (uniformUnits F)
  let C'' := C' + sk.2.1 • gen
  let U' := u • gen
  let V' := sk.1 • U' + u • C''
  let π' ← πis.prove H (sk.1 • H, C'', U', V') (sk.1, u)
  pure (some (U', V', π'))

/-- Issuance, user's first move of `μCMZ_AT` (O24 Figure 9): the core's
`atIssueUsr₁` lifted to the oracle carrier, the public parameters kept in the
state for the second move `credIssueUsr₂`. A separate definition: written
inline in the `issueUsr₁` field of `μCMZATSyntax`, its elaboration does not
terminate. -/
noncomputable def atIssueUsr₁PiIs {n : ℕ} (gen : G) (pp : Params G n) (m : Fin n → F) :
    OracleComp (ZKRO HS) ((F × G × Params G n) × G) :=
  (fun sC => ((sC.1, sC.2, pp), sC.2)) <$> liftM (atIssueUsr₁ gen pp m)

variable (F)

/--
The anonymous-token variant `μCMZ_AT` of O24 Figure 9, `π_iu` removed and `π_is`
kept, as an `ATSyntax` at the oracle carrier `OracleComp (ZKRO HS)`, over the
generator `gen` and the proof system `πis : ZKP_cmz.is`. The carriers are

- `UsrState _ := F × G × Params G n`, the blinding scalar `s`, the commitment
  `C'` and the public parameters, the credential's user state;
- `IssueMsg _ := G`, the commitment `C'`;
- `BlindToken _ := G × G × πis.Proof`, the pair `(U', V')` and `π_is`;
- `Token _ := Code G`, the MAC code `(U, V)`.
-/
noncomputable def μCMZATSyntax (gen : G) (πis : RisProofSystem HS G F) :
    ATSyntax (OracleComp (ZKRO HS)) where
  toKeyedSetupSyntax := μCMZCredKeyedSetup F HS gen
  Token := fun _ => Code G
  UsrState := fun {_ n} _ => F × G × Params G n
  IssueMsg := fun _ => G
  BlindToken := fun _ => G × G × πis.Proof
  issueUsr₁ := fun _ pp m => atIssueUsr₁PiIs HS gen pp m
  issueSrv := fun H sk C' => atIssueSrvPiIs HS gen H πis sk C'
  issueUsr₂ := fun H st resp => credIssueUsr₂ HS H πis st resp
  verify := fun _ sk m t => verify sk m t

/--
Correctness of `μCMZ_AT` (O24 Figure 9) at the oracle carrier,
`ATSyntax.CorrectRO` for `μCMZATSyntax`: the step the proof of Theorem 5.11
calls straightforward. The hypotheses are a nonzero generator and the perfect
completeness of `π_is` for `R_cmz.is`.

The lifted `setup`, `keygen` and first user move leave the cache `∅`;
`ProofSystemFor.verify_of_perfectlyComplete` discharges the verification of
`π_is`, and the unblinding algebra `V' − s·U' = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·U'` gives
the MAC equation, as in `credIssue_correct`.
-/
theorem μCMZAT_correctRO (gen : G) (hgen : gen ≠ 0) (πis : RisProofSystem HS G F)
    (his : πis.CompleteRO HS (fun k => (μCMZBaseMACSyntax F gen).setup k 0)
      (fun H x w => risRel (F := F) gen H x w)) :
    (μCMZATSyntax F HS gen πis).CorrectRO HS := by
  rintro secParam n _hn crs s₀ hcrs ⟨⟨x₀, xᵣ, x⟩, pp⟩ s₁ hkeys m σ? s₂ hσ
  -- The lifted `setup` and `keygen` leave the cache `∅`.
  obtain ⟨hH, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hcrs
  obtain ⟨hk, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hkeys
  obtain rfl := (mem_support_keygen (F := F) (G := G) crs gen x₀ xᵣ x pp).mp hk
  -- User, first move. The core's commitment, lifted.
  simp only [ATSyntax.issue, issueChain, μCMZATSyntax, atIssueUsr₁PiIs, atIssueSrvPiIs,
    bind_assoc, pure_bind, bind_map_left] at hσ
  obtain ⟨sC, c₁, hs, h₁⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp hσ
  obtain ⟨hsC, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hs
  simp only [atIssueUsr₁, support_bind, support_uniformSample, Set.mem_iUnion,
    Set.mem_univ, exists_const] at hsC
  obtain ⟨s, rfl⟩ := hsC
  -- Server. Sample the nonzero `u` and prove `π_is`.
  obtain ⟨u, c₂, hu₀, h₂⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₁
  obtain ⟨hu, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hu₀
  obtain ⟨π', c₃, hπ', h₃⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₂
  -- User, second move. The check `U' ≠ 0` passes and `π_is` verifies.
  have hU' : u • gen ≠ 0 := smul_ne_zero ((mem_support_uniformUnits F u).mp hu) hgen
  simp only [credIssueUsr₂, if_neg hU'] at h₃
  obtain ⟨b, c₄, hb, h₄⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₃
  -- The `R_cmz.is` witness goes inline: stating it in a `have` does not terminate.
  obtain rfl := ProofSystemFor.verify_of_perfectlyComplete HS πis _ _ his hH
    (decide_eq_true ⟨rfl, rfl, rfl⟩) hπ' hb
  obtain ⟨r, c₅, hr₀, h₅⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₄
  obtain ⟨hr, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hr₀
  obtain ⟨rfl, rfl⟩ := (mem_support_runRO_pure HS _ _ _ _).mp h₅
  -- The unblinded pair passes the base-MAC check.
  refine ⟨_, rfl, ?_⟩
  simp only [μCMZATSyntax, verify, macScalar, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨smul_ne_zero ((mem_support_uniformUnits F r).mp hr) hU', ?_⟩
  -- `r·(V' − s·U') = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·(r·U')`, module algebra over `gen`.
  have hsum (v : Fin n → F) : (∑ i, v i • (x i • gen)) = (∑ i, x i * v i) • gen := by
    simp only [Finset.sum_smul, smul_smul, mul_comm]
  rw [hsum m]
  module

end KVAC.Schemes.MicroCMZ
