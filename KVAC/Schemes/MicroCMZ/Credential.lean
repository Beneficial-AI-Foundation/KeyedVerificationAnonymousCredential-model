/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Construction
import KVAC.Schemes.MicroCMZ.ProofSystems
import KVAC.Framework.Syntax

/-!
# The μCMZ credential (O24 §5.1, Figure 9)

The keyed-verification credential μCMZ of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552 (O24), as an instance of the
Framework's `KVACSyntax` at the oracle carrier `OracleComp (ZKRO HS)`. The three
non-interactive proof systems `ZKP_cmz.iu`, `ZKP_cmz.is` and `ZKP_cmz.p` of
Figure 9 are parameters of the instance (`KVAC.Schemes.MicroCMZ.ProofSystems`),
so the instance does not depend on how they are constructed.

## Setup and key generation

Setup, key generation, the message space and the key types are those of the base
MAC `μCMZBaseMACSyntax`, with `setup` and `keygen` lifted from `ProbComp` into the
oracle carrier through `liftM`. The lifted computations never query the random
oracle, and `KVAC.Core.runRO_liftM` states that running them through `runRO`
leaves the cache unchanged.

## Issuance (Figure 9)

On public parameters `pp = (X₀, Xᵣ, X⃗)`, attributes `m⃗` and predicate `φ`:

- **User, first move.** Sample `s ←$ ℤ_p`, form `C' = Σᵢ mᵢ·Xᵢ + s·G`, and prove
  `π_iu` for the statement `(C', X⃗, φ)` with witness `(m⃗, s)`.
- **Server.** Verify `π_iu`, rejecting with `none` on failure. Sample `u ←$ ℤ_p×`,
  set `C'' = C' + Xᵣ`, `U' = u·G` and `V' = x₀·U' + u·C''`, and prove `π_is` for
  the statement `(X₀, C'', U', V')` with witness `(x₀, u)`.
- **User, second move.** Check `U' ≠ 0` and verify `π_is` on `(X₀, C' + Xᵣ, U', V')`,
  aborting with `none` on failure. Sample `r ←$ ℤ_p×` and unblind to the credential
  `(U, V) = (r·U', r·(V' − s·U'))`.

## Presentation (Figure 9)

- **User.** Sample `r ←$ ℤ_p×` and rerandomize the credential to `(U', V') = (r·U, r·V)`.
  Sample `r' ←$ ℤ_p` and `rᵢ ←$ ℤ_p`, commit `C_V = V' + r'·H` and
  `Cᵢ = mᵢ·U' + rᵢ·G`, set `Z = Σᵢ rᵢ·Xᵢ − r'·H`, and prove `π_p` for the statement
  `(U', X⃗, C⃗, Z, φ)` with witness `(r', r⃗, m⃗)`.
- **Server.** Recompute `Z = (x₀ + xᵣ)·U' + Σᵢ xᵢ·Cᵢ − C_V` and accept iff
  `U' ≠ 0` and `π_p` verifies on `(U', X⃗, C⃗, Z, φ)`.

## Sampling, and the bases the server recomputes

Both issuance nonces `u`, `r` and the presentation rerandomizer `r` are drawn
from the nonzero scalars, where Figure 9 prints `ℤ_p`. §5.1 states the
rerandomization property for `r ≠ 0` and samples the presentation rerandomizer
from `ℤ_p×`. Errata item 8 records the mismatch for the issuance nonces, and the
anonymous-token core `ATVariant.lean` draws them the same way.

The server's input is `sk` alone, so it recomputes the public bases `X⃗`, `X₀` and
`Xᵣ` from the secret key and the crs.

## The predicate family

Predicates are the Boolean policies `Policy F n` of `Relations.lean`, with the
trivial policy, pointwise conjunction and the full-disclosure policy `φ_m⃗`. The
partial-disclosure members `φ_a⃗` arrive with issue #104.

## Out of scope

Correctness at the oracle carrier (`CorrectRO`), the security statements and the
blueprint anchoring follow in separate PRs of issue #163.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

/-! ## Sampling, in `ProbComp` -/

/-- The user's issuance coins, the blinding scalar `s ←$ ℤ_p`. -/
noncomputable def credIssueCoins : ProbComp F := $ᵗ F

/-- The presentation coins `(r, r', r⃗)`, the rerandomizer `r ←$ ℤ_p×`, the blinding
scalar `r' ←$ ℤ_p` of `C_V` and the commitment randomness `rᵢ ←$ ℤ_p` for each `i`. -/
noncomputable def credPresentCoins (n : ℕ) : ProbComp (F × F × (Fin n → F)) := do
  let r ← uniformUnits F
  let r' ← $ᵗ F
  let rs ← $ᵗ (Fin n → F)
  pure (r, r', rs)

/-! ## The public bases recomputed from the secret key -/

/-- The attribute bases `X⃗ = x⃗·G` of the secret key `sk = (x₀, xᵣ, x⃗)`. -/
def credBases {n : ℕ} (gen : G) (sk : Key F n) : PublicBases G n :=
  fun i => sk.2.2 i • gen

variable (HS : HashSpec)

/-! ## Issuance -/

/-- Issuance, user's first move (O24 Figure 9). Sample `s ←$ ℤ_p`, send
`C' = Σᵢ mᵢ·Xᵢ + s·G` with the proof `π_iu` for `(C', X⃗, φ)`, and keep
`(s, C', pp)` as state. -/
noncomputable def credIssueUsr₁ {n : ℕ} (gen H : G) (πiu : RiuProofSystem HS G F n)
    (pp : Params G n) (m : Fin n → F) (φ : Policy F n) :
    OracleComp (ZKRO HS) ((F × G × Params G n) × (G × πiu.Proof)) := do
  let s ← liftM (credIssueCoins (F := F))
  let C' := (∑ i, m i • pp.2.2 i) + s • gen
  let π ← πiu.prove H (C', pp.2.2, φ) (m, s)
  pure ((s, C', pp), (C', π))

/-- Issuance, server's move (O24 Figure 9). Verify `π_iu` and reject with `none` on
failure. Otherwise sample `u ←$ ℤ_p×` and answer `U' = u·G`,
`V' = x₀·U' + u·(C' + Xᵣ)` with the proof `π_is` for `(X₀, C' + Xᵣ, U', V')`. -/
noncomputable def credIssueSrv {n : ℕ} (gen H : G) (πiu : RiuProofSystem HS G F n)
    (πis : RisProofSystem HS G F) (sk : Key F n) (φ : Policy F n)
    (μ : G × πiu.Proof) : OracleComp (ZKRO HS) (Option (G × G × πis.Proof)) := do
  let (C', π) := μ
  if ← πiu.verify H (C', credBases gen sk, φ) π then
    let u ← liftM (uniformUnits F)
    let C'' := C' + sk.2.1 • gen
    let U' := u • gen
    let V' := sk.1 • U' + u • C''
    let π' ← πis.prove H (sk.1 • H, C'', U', V') (sk.1, u)
    pure (some (U', V', π'))
  else
    pure none

/-- Issuance, user's second move (O24 Figure 9). Check `U' ≠ 0` and verify `π_is`
on `(X₀, C' + Xᵣ, U', V')`, aborting with `none` on failure. Otherwise sample
`r ←$ ℤ_p×` and unblind to the credential `(r·U', r·(V' − s·U'))`. -/
noncomputable def credIssueUsr₂ {n : ℕ} (H : G) (πis : RisProofSystem HS G F)
    (st : F × G × Params G n) (resp : G × G × πis.Proof) :
    OracleComp (ZKRO HS) (Option (Code G)) := do
  let (s, C', pp) := st
  let (U', V', π') := resp
  if U' = 0 then
    pure none
  else if ← πis.verify H (pp.1, C' + pp.2.1, U', V') π' then
    let r ← liftM (uniformUnits F)
    pure (some (r • U', r • (V' - s • U')))
  else
    pure none

/-! ## Presentation -/

/-- Presentation, user side (O24 Figure 9). Rerandomize the credential with
`r ←$ ℤ_p×`, commit `C_V = V' + r'·H` and `Cᵢ = mᵢ·U' + rᵢ·G`, and prove `π_p` for
`(U', X⃗, C⃗, Z, φ)` with `Z = Σᵢ rᵢ·Xᵢ − r'·H`. -/
noncomputable def credPresentUsr {n : ℕ} (gen H : G) (πp : RpProofSystem HS G F n)
    (pp : Params G n) (m : Fin n → F) (σ : Code G) (φ : Policy F n) :
    OracleComp (ZKRO HS) (G × G × (Fin n → G) × πp.Proof) := do
  let (r, r', rs) ← liftM (credPresentCoins (F := F) n)
  let U' := r • σ.1
  let V' := r • σ.2
  let CV := V' + r' • H
  let C : Fin n → G := fun i => m i • U' + rs i • gen
  let Z := (∑ i, rs i • pp.2.2 i) - r' • H
  let π ← πp.prove H (U', pp.2.2, C, Z, φ) (r', rs, m)
  pure (U', CV, C, π)

/-- Presentation, server side (O24 Figure 9). Recompute
`Z = (x₀ + xᵣ)·U' + Σᵢ xᵢ·Cᵢ − C_V` and accept iff `U' ≠ 0` and `π_p` verifies on
`(U', X⃗, C⃗, Z, φ)`. The check `U' ≠ 0` lies outside `R_cmz.p`, and footnote 5 of
O24 §5.1 states that it is required. The verification of `π_p` on this `Z` is what
tests the MAC equation, since `V'` and `m⃗` stay hidden. -/
noncomputable def credPresentSrv {n : ℕ} (gen H : G) (πp : RpProofSystem HS G F n)
    (sk : Key F n) (φ : Policy F n) (ρ : G × G × (Fin n → G) × πp.Proof) :
    OracleComp (ZKRO HS) Bool := do
  let (U', CV, C, π) := ρ
  let Z := (sk.1 + sk.2.1) • U' + (∑ i, sk.2.2 i • C i) - CV
  let ok ← πp.verify H (U', credBases gen sk, C, Z, φ) π
  pure (decide (U' ≠ 0) && ok)

/-! ## The instance -/

variable (F)

/-- The keyed setup of the μCMZ credential at the oracle carrier. The carriers are
those of `μCMZBaseMACSyntax`, and `setup` and `keygen` are its algorithms lifted
through `liftM`. -/
noncomputable def μCMZCredKeyedSetup (gen : G) : KeyedSetupSyntax (OracleComp (ZKRO HS)) where
  Crs := (μCMZBaseMACSyntax F gen).Crs
  Msg := (μCMZBaseMACSyntax F gen).Msg
  DecidableEqMsg := (μCMZBaseMACSyntax F gen).DecidableEqMsg
  Sk := (μCMZBaseMACSyntax F gen).Sk
  Pp := (μCMZBaseMACSyntax F gen).Pp
  setup := fun secParam n => liftM ((μCMZBaseMACSyntax F gen).setup secParam n)
  keygen := fun crs => liftM ((μCMZBaseMACSyntax F gen).keygen crs)

/--
The μCMZ credential (O24 §5.1, Figure 9) as a `KVACSyntax` at the oracle carrier
`OracleComp (ZKRO HS)`, over the generator `gen` and the proof systems
`πiu n : ZKP_cmz.iu`, `πis : ZKP_cmz.is` and `πp n : ZKP_cmz.p`. The proof systems
of `R_cmz.iu` and `R_cmz.p` are families in `n`, since their statements carry the
`n` attribute bases.

The carriers are

- `Pred _ := Policy F n`, the Boolean policies on attribute vectors.
- `UsrState _ := F × G × Params G n`, the blinding scalar `s`, the commitment `C'`
  and the public parameters.
- `IssueMsg _ := G × (πiu n).Proof`, the commitment `C'` and `π_iu`.
- `BlindCred _ := G × G × πis.Proof`, the pair `(U', V')` and `π_is`.
- `Cred _ := Code G`, the MAC code `(U, V)`.
- `PresentMsg _ := G × G × (Fin n → G) × (πp n).Proof`, the tuple `(U', C_V, C⃗)`
  and `π_p`.
-/
noncomputable def μCMZCredentialSyntax (gen : G)
    (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
    (πp : ∀ n, RpProofSystem HS G F n) : KVACSyntax (OracleComp (ZKRO HS)) where
  toKeyedSetupSyntax := μCMZCredKeyedSetup F HS gen
  Pred := fun {_ n} _ => Policy F n
  holds := fun _ φ m => φ m
  trivialPred := fun _ => trivialPolicy
  holds_trivialPred := fun _ _ => rfl
  andPred := fun _ φ ψ => andPolicy φ ψ
  holds_andPred := fun _ _ _ _ => rfl
  DecidableEqPred := fun _ => inferInstance
  Cred := fun _ => Code G
  UsrState := fun {_ n} _ => F × G × Params G n
  IssueMsg := fun {_ n} _ => G × (πiu n).Proof
  BlindCred := fun _ => G × G × πis.Proof
  PresentMsg := fun {_ n} _ => G × G × (Fin n → G) × (πp n).Proof
  DecidableEqPresentMsg := fun {_ n} _ =>
    have : DecidableEq ((Fin n → G) × (πp n).Proof) := inferInstance
    inferInstance
  exactPred := fun _ m => exactPolicy m
  holds_exactPred := fun _ m m' => exactPolicy_eq_true_iff m m'
  issueUsr₁ := fun {_ n} H pp m φ => credIssueUsr₁ HS gen H (πiu n) pp m φ
  issueSrv := fun {_ n} H sk φ μ => credIssueSrv HS gen H (πiu n) πis sk φ μ
  issueUsr₂ := fun H st resp => credIssueUsr₂ HS H πis st resp
  presentUsr := fun {_ n} H pp m σ φ => credPresentUsr HS gen H (πp n) pp m σ φ
  presentSrv := fun {_ n} H sk φ ρ => credPresentSrv HS gen H (πp n) sk φ ρ

end KVAC.Schemes.MicroCMZ
