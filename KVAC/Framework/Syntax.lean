/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Framework.PredicateFamily

/-!
# Keyed-verification credential system — syntax (O24 Definition 4.2)

The syntactic algorithms of a keyed-verification anonymous credential
system, following Orrù, *Revisiting Keyed-Verification Anonymous
Credentials*, IACR ePrint 2024/1552 (O24), Definition 4.2. The credential
predicate family (Definition 4.1) lives in `PredicateFamily.lean`.

Layered like the algebraic MAC (`KVAC.Core.AlgebraicMAC`): the algorithms
live here as a monad-polymorphic structure, and the semantic obligations
sit in their own files.

- `KVACSyntax M` (this file) — the Definition 4.2 algorithms, no obligations.
- `Correct` (`Correctness.lean`) — Definition 4.3.
- Anonymity (Definition 4.4) and extractability (Definition 4.5, Figure 8) —
  deferred to later tracks.

## Protocol shape

Every O24 protocol is one-round, so we split each into non-interactive
algorithms as the paper does:

- Issuance: `I.Usr₁` (the user's request), `I.Srv` (the issuer's response,
  which may reject), `I.Usr₂` (the user checks and unblinds, and may abort).
- Presentation: `P.Usr` (the user's proof), `P.Srv` (accept/reject).

Rejection and abort are the `Option` results of `I.Srv` and `I.Usr₂` — the
paper's `σ' = ⊥` and its `check` lines in Figure 9.

## Layering

This file adds only the Definition 4.2 issuance/presentation algorithms. The
carriers beneath them come from the tower `KVACSyntax` extends:

- `KeyedSetupSyntax` (`KVAC.Core.KeyedSetup`) — CRS, message space,
  `setup`/`keygen`.
- `PredicateFamily` (`PredicateFamily.lean`) — the Definition 4.1 predicate
  family `Pred`/`holds` with its trivial-predicate and conjunction laws.
-/

namespace KVAC.Framework

/--
Syntactic keyed-verification credential system (O24 Definition 4.2).

`kvac : KVACSyntax M` extends `PredicateFamily M` (and, through it,
`KeyedSetupSyntax M`) with the issuance and presentation algorithms
`I.{Usr₁,Srv,Usr₂} / P.{Usr,Srv}`, over an abstract randomness monad `M`. The
setup and key-generation algorithms `S / K` and the Definition 4.1 predicate
family come from the extended structures; this layer adds only the following
carriers, all selected by the CRS:

- `Cred` — credentials `σ`.
- `UsrState` — the user's issuance state `st_u`.
- `IssueMsg`, `BlindCred` — the issuance request `μ` and response `σ'`.
- `PresentMsg` — the presentation message `ρ`.

Correctness and the security games are standalone predicates on a
`KVACSyntax ProbComp`, not fields — matching `AlgebraicMACSyntax`.
-/
structure KVACSyntax (M : Type → Type) [Monad M]
    extends PredicateFamily M where
  /-- Credential type `σ`, selected by the CRS. -/
  Cred : {secParam n : Nat} → Crs secParam n → Type
  /-- User issuance state `st_u`, selected by the CRS. -/
  UsrState : {secParam n : Nat} → Crs secParam n → Type
  /-- User issuance-request message `μ`, selected by the CRS. -/
  IssueMsg : {secParam n : Nat} → Crs secParam n → Type
  /-- Issuer blinded-credential response `σ'`, selected by the CRS. -/
  BlindCred : {secParam n : Nat} → Crs secParam n → Type
  /-- Presentation message `ρ`, selected by the CRS. -/
  PresentMsg : {secParam n : Nat} → Crs secParam n → Type
  /-- Issuance, user's first move: `(st_u, μ) ← KVAC.I.Usr₁(pp, m⃗, φ)`. -/
  issueUsr₁ : {secParam n : Nat} → (crs : Crs secParam n) → Pp crs →
    (Fin n → Msg crs) → Pred crs → M (UsrState crs × IssueMsg crs)
  /-- Issuance, issuer's move: `σ' ← KVAC.I.Srv(sk, φ, μ)`. Returns `none`
  when the issuer rejects the user's message (the paper's `σ' = ⊥`). -/
  issueSrv : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    Pred crs → IssueMsg crs → M (Option (BlindCred crs))
  /-- Issuance, user's second move: `σ ← KVAC.I.Usr₂(st_u, σ')`. Returns
  `none` when the user's checks on the issuer's response fail (the `check`
  lines of O24 Figure 9). -/
  issueUsr₂ : {secParam n : Nat} → (crs : Crs secParam n) → UsrState crs →
    BlindCred crs → M (Option (Cred crs))
  /-- Presentation, user side: `ρ ← KVAC.P.Usr(pp, m⃗, σ, φ)`. -/
  presentUsr : {secParam n : Nat} → (crs : Crs secParam n) → Pp crs →
    (Fin n → Msg crs) → Cred crs → Pred crs → M (PresentMsg crs)
  /-- Presentation, issuer side: `0/1 ← KVAC.P.Srv(sk, φ, ρ)`. `M`-valued
  (unlike the MAC's deterministic `verify`) so oracle-querying verifiers
  like Fiat–Shamir fit. -/
  presentSrv : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    Pred crs → PresentMsg crs → M Bool

namespace KVACSyntax

variable {M : Type → Type} [Monad M] (kvac : KVACSyntax M)
variable {secParam n : Nat}

/--
The full one-round issuance interaction `⟨I.Usr(pp, m⃗, φ) ⇌ I.Srv(sk, φ)⟩`
over an arbitrary predicate `φ`: the user's first move, the issuer's response,
and the user's unblinding, chained. `none` propagates either the issuer's
rejection or the user's abort. The paper's shorthand `KVAC.M(sk, m⃗)` (O24 §4.1)
is the special case `φ = φ_m⃗`. -/
def issue (crs : kvac.Crs secParam n) (sk : kvac.Sk crs) (pp : kvac.Pp crs)
    (m : kvac.MsgVec crs) (φ : kvac.Pred crs) : M (Option (kvac.Cred crs)) := do
  let (stU, μ) ← kvac.issueUsr₁ crs pp m φ
  match ← kvac.issueSrv crs sk φ μ with
  | none => pure none
  | some σ' => kvac.issueUsr₂ crs stU σ'

/--
The full one-round presentation interaction `⟨P.Srv(sk, φ) ⇌ P.Usr(pp, m⃗, σ, φ)⟩`
over an arbitrary predicate `φ`: the user's proof followed by the issuer's
check. The paper's shorthand `KVAC.V(sk, m⃗, σ)` (O24 §4.1) is the special case
`φ = φ_m⃗` (the exact-attribute predicate), not the trivial `φ₁`. -/
def present (crs : kvac.Crs secParam n) (sk : kvac.Sk crs) (pp : kvac.Pp crs)
    (m : kvac.MsgVec crs) (σ : kvac.Cred crs) (φ : kvac.Pred crs) : M Bool := do
  let ρ ← kvac.presentUsr crs pp m σ φ
  kvac.presentSrv crs sk φ ρ

end KVACSyntax

end KVAC.Framework
