/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.KeyedSetup

/-!
# Anonymous tokens — syntactic layer (O24 §3.4)

The syntax of anonymous-token schemes, following Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552 (O24),
§3.4. An anonymous token is a "blind MAC": the user obtains a token `σ`
on an attribute vector `m⃗` kept hidden from the issuer, and the issuer
later verifies `(m⃗, σ)` directly with its secret key. Unlike a full
credential system (O24 Definition 4.2) there are no predicates and no
presentation protocol — redemption reveals the message.

This file holds only the algorithms. Correctness lives in
`Correctness.lean`, the one-more unforgeability game in `Security.lean`,
and the paper-level bundle in the umbrella
`KVAC.Preliminaries.AnonymousTokens`.

## Design notes

**The server may reject.** `issueSrv` returns an `Option`, matching
`KVACSyntax.issueSrv`: dropping the user's issuance proof does not remove
every server-side check — μBBS_AT's server keeps its `C′ ≠ 0_G` test (O24
Figure 10 boxes only the proof) — so the abstract interface must carry
rejection. μCMZ_AT's server happens to answer unconditionally. The *user*
may also abort while unblinding — `issueUsr₂` returns an `Option`,
matching `KVACSyntax.issueUsr₂` and the `check` steps of the concrete
schemes.
-/

namespace KVAC.Preliminaries

open KVAC.Core

/--
Syntactic anonymous-token scheme per O24 §3.4: `AT = (S, K, I, V)` for
`n` attributes over a CRS-selected attribute space.

Extends `KeyedSetupSyntax` (the CRS, message space, and `setup`/`keygen`
algorithms `S` / `K`), and adds the token-specific carriers and the
issuance/verification algorithms. The one-round issuance protocol
`⟨I.Usr(pp, m⃗) ⇌ I.Srv(sk)⟩` is split into its non-interactive moves as
the paper does for credential systems:

- `issueUsr₁` — the user blinds `m⃗` into a request `µ`, keeping state;
- `issueSrv` — the server answers with a blinded token `σ'`, or rejects;
- `issueUsr₂` — the user checks and unblinds to the token `σ`, or aborts.

`verify` is the keyed verification `AT.V(sk, m⃗, σ)`, deterministic like
the algebraic MAC's — redemption reveals `m⃗`, so no proof (and hence no
oracle) is involved in checking a token.
-/
structure ATSyntax (M : Type → Type) [Monad M]
    extends KeyedSetupSyntax M where
  /-- Token type `σ`, selected by the CRS. -/
  Token : {secParam n : Nat} → Crs secParam n → Type
  /-- User issuance state, selected by the CRS. -/
  UsrState : {secParam n : Nat} → Crs secParam n → Type
  /-- User issuance-request message `µ`, selected by the CRS. -/
  IssueMsg : {secParam n : Nat} → Crs secParam n → Type
  /-- Server blinded-token response `σ'`, selected by the CRS. -/
  BlindTok : {secParam n : Nat} → Crs secParam n → Type
  /-- Issuance, user's first move: `(st, µ) ← AT.I.Usr₁(pp, m⃗)`. -/
  issueUsr₁ : {secParam n : Nat} → (crs : Crs secParam n) → Pp crs →
    (Fin n → Msg crs) → M (UsrState crs × IssueMsg crs)
  /-- Issuance, server's move: `σ' ← AT.I.Srv(sk, µ)`. Returns `none` when
  the server rejects the user's message — μCMZ_AT's server answers
  unconditionally, but μBBS_AT's keeps its `C′ ≠ 0_G` check (O24 Figure 10),
  so the interface carries rejection like `KVACSyntax.issueSrv`. -/
  issueSrv : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    IssueMsg crs → M (Option (BlindTok crs))
  /-- Issuance, user's second move: `σ ← AT.I.Usr₂(st, σ')`. Returns `none`
  when the user's checks on the server's response fail. -/
  issueUsr₂ : {secParam n : Nat} → (crs : Crs secParam n) → UsrState crs →
    BlindTok crs → M (Option (Token crs))
  /-- Verification `0/1 ← AT.V(sk, m⃗, σ)`. -/
  verify : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    (Fin n → Msg crs) → Token crs → Bool

namespace ATSyntax

variable {M : Type → Type} [Monad M] (tok : ATSyntax M)
variable {secParam n : Nat}

/--
The full one-round issuance interaction `⟨I.Usr(pp, m⃗) ⇌ I.Srv(sk)⟩`:
the user's request, the server's response, and the user's unblinding,
chained. `none` propagates either the server's rejection or the user's
abort.
-/
def issue (crs : tok.Crs secParam n) (sk : tok.Sk crs) (pp : tok.Pp crs)
    (m : tok.MsgVec crs) : M (Option (tok.Token crs)) := do
  let (st, μ) ← tok.issueUsr₁ crs pp m
  match ← tok.issueSrv crs sk μ with
  | none => pure none
  | some resp => tok.issueUsr₂ crs st resp

end ATSyntax

end KVAC.Preliminaries
