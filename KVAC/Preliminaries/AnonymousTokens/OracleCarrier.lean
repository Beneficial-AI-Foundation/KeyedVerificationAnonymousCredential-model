/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Preliminaries.AnonymousTokens.Security
import KVAC.Core.NIZKP.Security

/-!
# Anonymous tokens at the oracle carrier `OracleComp (ZKRO H)` (O24 §3.4, Figure 6)

A scheme whose server attaches a Fiat–Shamir proof, such as the printed μCMZ_AT
of O24 Figure 9 with its issuance proof `π_is`, runs over
`OracleComp (ZKRO H)`, not `ProbComp`. This file states correctness and
one-more unforgeability at that carrier. The design is in
`DESIGN_ALTERNATIVES.md`, *Two carriers for one-more unforgeability*.

## Layout

- `ATSyntax.CorrectRO` — correctness, with setup, key generation and issuance
  threading one random-oracle cache, mirroring `KVAC.Framework.CorrectRO`.
- `OMUFAdversaryRO`, `OMUFGameRO`, `OMUFAdvRO` — the Figure 6 game at the
  oracle carrier: `omufExp` of `KVAC.Preliminaries.AnonymousTokens.Security`
  run through `runRO`.

## The cache

The experiment runs through one `runRO` from the empty cache: setup, key
generation, the server's proofs and the adversary's own hash queries all share
it. The extraction game of `KVAC.Framework.Extractability` threads one cache
through its phases the same way. Without sharing, an adversary could not check
a proof against the oracle the server proved under.
-/

namespace KVAC.Preliminaries

open OracleSpec OracleComp ENNReal KVAC.Core

/-! ## Correctness -/

namespace ATSyntax

/--
Correctness at the oracle carrier `OracleComp (ZKRO H)`: `Correct` with setup,
key generation and issuance run through `runRO`, threading one cache
`∅ → s₀ → s₁ → s₂`, so that a scheme's Fiat–Shamir proofs share the oracle.
Mirrors `KVAC.Framework.CorrectRO` for credentials.
-/
def CorrectRO (H : HashSpec) (tok : ATSyntax (OracleComp (ZKRO H))) : Prop :=
  ∀ (secParam n : Nat), 0 < n →
  ∀ (crs : tok.Crs secParam n) (s₀ : H.spec.QueryCache),
    (crs, s₀) ∈ support (runRO H ∅ (tok.setup secParam n)) →
  ∀ (keys : tok.Sk crs × tok.Pp crs) (s₁ : H.spec.QueryCache),
    (keys, s₁) ∈ support (runRO H s₀ (tok.keygen crs)) →
  ∀ (m : tok.MsgVec crs) (σ? : Option (tok.Token crs)) (s₂ : H.spec.QueryCache),
    (σ?, s₂) ∈ support (runRO H s₁ (tok.issue crs keys.1 keys.2 m)) →
      ∃ σ, σ? = some σ ∧ tok.verify crs keys.1 m σ = true

end ATSyntax

/-! ## The game -/

/-- An OMUF adversary at the oracle carrier: the shape of `OMUFAdversary`, with
the random oracle `ZKRO H`, which includes uniform sampling, in place of
`unifSpec`. -/
structure OMUFAdversaryRO (H : HashSpec) (tok : ATSyntax (OracleComp (ZKRO H))) where
  /-- The adversary's program: from `(crs, pp)`, query the random oracle and
  Sign / Verify, and output the candidate message/token pairs. -/
  run : {secParam n : Nat} → (crs : tok.Crs secParam n) → tok.Pp crs →
    OracleComp (ZKRO H + OMUFOracleSpec tok crs)
      (List (tok.MsgVec crs × tok.Token crs))

/-- The one-more unforgeability experiment (O24 Figure 6) at the oracle carrier:
`omufExp` with the adversary's random-oracle queries forwarded to the
experiment's own oracle, run through `runRO` from the empty cache. -/
def OMUFGameRO (H : HashSpec) (tok : ATSyntax (OracleComp (ZKRO H)))
    (A : OMUFAdversaryRO H tok) (secParam n : Nat) : ProbComp Bool :=
  Prod.fst <$> runRO H ∅ (omufExp tok secParam n A.run)

/-- The OMUF advantage at the oracle carrier, `Pr[= true | OMUFGameRO …]`. -/
noncomputable abbrev OMUFAdvRO (H : HashSpec) (tok : ATSyntax (OracleComp (ZKRO H)))
    (A : OMUFAdversaryRO H tok) (secParam n : Nat) : ℝ≥0∞ :=
  Pr[= true | OMUFGameRO H tok A secParam n]

end KVAC.Preliminaries
