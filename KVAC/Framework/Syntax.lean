/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/

/-!
# Keyed-verification credential system — syntactic layer (O24 Definitions 4.1, 4.2)

Syntactic part of a keyed-verification anonymous credential system per Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
(O24), Definitions 4.1 and 4.2.

The paper-level object is layered exactly like the algebraic MAC
(`KVAC.Core.AlgebraicMAC`):

- **`KVACSyntax M`** (this file) — the algorithms of Definition 4.2 with no
  semantic obligations, polymorphic in the randomness monad `M`.
- **`Correct`** (in `Correctness.lean`) — Definition 4.3, support-based.
- **Anonymity** game + advantage (in `Anonymity.lean`) — Definition 4.4.
- **Extractability** game (Definition 4.5, O24 Figure 8) — deferred to the
  extractability track.

## Protocol shape (O24 §4.1)

All issuance and presentation protocols in O24 are one-round, so the paper
splits them into non-interactive algorithms, which we adopt verbatim:

- Issuance `KVAC.I`:
  `(st_u, μ) ← I.Usr₁(pp, m⃗, φ)`, then `σ' ← I.Srv(sk, φ, μ)` (the issuer may
  reject, returning `⊥`), then `σ ← I.Usr₂(st_u, σ')` (the user checks the
  issuer's response and may abort).
- Presentation `KVAC.P`:
  `ρ ← P.Usr(pp, m⃗, σ, φ)`, then `0/1 ← P.Srv(sk, φ, ρ)`.

Rejection/abort is modeled with `Option` on the *output* side of `I.Srv` and
`I.Usr₂` (the paper's `σ' = ⊥` and the user's `check` lines in Figure 9).

## Predicates (O24 Definition 4.1)

A credential predicate is an efficiently-computable Boolean function on
attribute vectors; a predicate family contains the trivial predicate and is
closed under conjunction. Predicates are *data* (they are inputs to the
algorithms and statements of the associated zero-knowledge proofs), so the
structure carries a per-CRS type `Pred` of predicate descriptions together
with its Boolean semantics `holds`, the trivial predicate, and conjunction —
the closure properties of Definition 4.1 become structure fields.

## Design notes

Carrier families are intrinsically typed by the CRS, and the structure is
monad-polymorphic, both exactly as in `AlgebraicMACSyntax` — see the design
notes in `KVAC/Core/AlgebraicMAC/Construction.lean`.
-/

namespace KVAC.Core

/--
Syntactic keyed-verification credential system per O24 Definition 4.2, with
the predicate family of Definition 4.1 carried as structure fields.

A value `kvac : KVACSyntax M` packages the algorithms
`S / K / I.{Usr₁,Srv,Usr₂} / P.{Usr,Srv}` under an abstract monad `M`.
Carrier type families (all selected by the CRS):

- `Msg` — attribute type; the system operates on `Fin n → Msg crs`.
- `Pred` — predicate descriptions `φ ∈ Φ`, with semantics `holds`.
- `Sk`, `Pp` — the issuer's secret key and public parameters.
- `Cred` — credentials `σ`.
- `UsrState` — the user's issuance state `st_u`.
- `IssueMsg` — the user's issuance-request message `μ`.
- `BlindCred` — the issuer's blinded-credential response `σ'`.
- `PresentMsg` — the presentation message `ρ`.

Correctness and the security games are *not* fields — they are standalone
predicates on a `KVACSyntax ProbComp` (`Correctness.lean`, `Anonymity.lean`),
matching the layering of `AlgebraicMACSyntax`.
-/
structure KVACSyntax (M : Type → Type) [Monad M] where
  /-- Common-reference-string type, indexed by security parameter and
  attribute count (O24 `crs ← KVAC.S(1^λ, n)`). -/
  Crs : Nat → Nat → Type
  /-- Attribute (message) type, selected by the CRS. -/
  Msg : {secParam n : Nat} → Crs secParam n → Type
  /-- Predicate descriptions `φ ∈ Φ` (O24 Definition 4.1), selected by the
  CRS. Predicates are data because they are inputs to issuance and
  presentation. -/
  Pred : {secParam n : Nat} → Crs secParam n → Type
  /-- Boolean semantics of a predicate on an attribute vector: O24's
  `φ(m⃗) ∈ {0,1}` (efficiently computable, hence `Bool`). -/
  holds : {secParam n : Nat} → (crs : Crs secParam n) → Pred crs →
    (Fin n → Msg crs) → Bool
  /-- The trivial predicate `φ₁` that every attribute vector satisfies
  (O24 Definition 4.1: every family contains it). -/
  trivialPred : {secParam n : Nat} → (crs : Crs secParam n) → Pred crs
  /-- `φ₁` accepts everything. -/
  holds_trivialPred : ∀ {secParam n : Nat} (crs : Crs secParam n)
    (m : Fin n → Msg crs), holds crs (trivialPred crs) m = true
  /-- Conjunction of predicates (O24 Definition 4.1: families are closed
  under conjunction). -/
  andPred : {secParam n : Nat} → (crs : Crs secParam n) → Pred crs →
    Pred crs → Pred crs
  /-- `andPred` is semantic conjunction. -/
  holds_andPred : ∀ {secParam n : Nat} (crs : Crs secParam n)
    (φ φ' : Pred crs) (m : Fin n → Msg crs),
    holds crs (andPred crs φ φ') m = (holds crs φ m && holds crs φ' m)
  /-- Secret-key type, selected by the CRS. -/
  Sk : {secParam n : Nat} → Crs secParam n → Type
  /-- Public-parameter type, selected by the CRS. -/
  Pp : {secParam n : Nat} → Crs secParam n → Type
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
  /-- Decidable equality on the attribute type (needed by the security
  games' freshness checks; an implementation requirement, not an
  assumption — cf. `AlgebraicMACSyntax.DecidableEqMsg`). -/
  DecidableEqMsg : {secParam n : Nat} → (crs : Crs secParam n) →
    DecidableEq (Msg crs)
  /-- Setup `crs ← KVAC.S(1^λ, n)`. -/
  setup : (secParam n : Nat) → M (Crs secParam n)
  /-- Key generation `(sk, pp) ← KVAC.K(crs)`. -/
  keygen : {secParam n : Nat} → (crs : Crs secParam n) →
    M (Sk crs × Pp crs)
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
  (unlike the MAC's deterministic `verify`) so that oracle-querying
  verifiers, e.g. Fiat–Shamir, fit the API. -/
  presentSrv : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    Pred crs → PresentMsg crs → M Bool

namespace KVACSyntax

variable {M : Type → Type} [Monad M] (kvac : KVACSyntax M)
variable {secParam n : Nat}

/-- The `DecidableEqMsg` field promoted to a typeclass instance. -/
instance (crs : kvac.Crs secParam n) : DecidableEq (kvac.Msg crs) :=
  kvac.DecidableEqMsg crs

/-- An `n`-attribute vector under the CRS (O24's `m⃗ ∈ M^n`). -/
abbrev MsgVec (crs : kvac.Crs secParam n) : Type := Fin n → kvac.Msg crs

/--
The full one-round issuance protocol
`σ ← (KVAC.I.Usr(pp, m⃗, φ) ⇌ KVAC.I.Srv(sk, φ))`: user's first move, issuer's
response, user's unblinding. `none` propagates both the issuer's rejection
and the user's abort. Together with `present` below this gives the paper's
shorthand `KVAC.M(sk, m⃗)` (O24 §4.1). -/
def issue (crs : kvac.Crs secParam n) (sk : kvac.Sk crs) (pp : kvac.Pp crs)
    (m : kvac.MsgVec crs) (φ : kvac.Pred crs) : M (Option (kvac.Cred crs)) := do
  let (stU, μ) ← kvac.issueUsr₁ crs pp m φ
  match ← kvac.issueSrv crs sk φ μ with
  | none => pure none
  | some σ' => kvac.issueUsr₂ crs stU σ'

/--
The full one-round presentation protocol
`0/1 ← (KVAC.P.Srv(sk, φ) ⇌ KVAC.P.Usr(pp, m⃗, σ, φ))`: the paper's shorthand
`KVAC.V(sk, m⃗, σ)` when `φ` is the trivial predicate (O24 §4.1). -/
def present (crs : kvac.Crs secParam n) (sk : kvac.Sk crs) (pp : kvac.Pp crs)
    (m : kvac.MsgVec crs) (σ : kvac.Cred crs) (φ : kvac.Pred crs) : M Bool := do
  let ρ ← kvac.presentUsr crs pp m σ φ
  kvac.presentSrv crs sk φ ρ

end KVACSyntax

end KVAC.Core
