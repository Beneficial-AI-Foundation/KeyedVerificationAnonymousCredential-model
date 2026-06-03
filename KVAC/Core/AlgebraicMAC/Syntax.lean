/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/

/-!
# Algebraic MAC — syntactic layer (O24 Definition 3.1)

Syntactic part of an algebraic message authentication code per Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
Definition 3.1.

The paper-level `AlgebraicMAC` object is layered:

- **`AlgebraicMACSyntax M`** (this file) — bundles the four algorithms
  Setup / KeyGen / MAC / Verify with no semantic obligations. Polymorphic
  in the monad `M` encoding randomness (`Id`, `ProbComp`, future symbolic
  monads, …).
- **`Correct`** (in `Correctness.lean`) — functional correctness predicate
  on an `AlgebraicMACSyntax ProbComp`, stated as a support-based equation.
- **UF-CMVA** game + advantage (in `UFCMVA.lean`) — security predicate on
  an `AlgebraicMACSyntax ProbComp`, in line with O24 Figure 5.
- **`AlgebraicMAC`** (in `KVAC.Core.AlgebraicMAC`, the umbrella file) —
  the paper-level object: an `AlgebraicMACSyntax ProbComp` together with
  a proof of `Correct`.

Splitting syntax / correctness / security into separate files follows the
convention requested in PR #24 review (separate file per security
property, e.g. as in the `proof-ladders` repo), so that concrete schemes
can import only what they need.

## Design notes

### Intrinsic typing of the carrier families

`Crs : Nat → Nat → Type` makes the CRS type *depend* on both `secParam`
and `n`. Downstream carrier types (`Msg`, `Sk`, `Pp`, `Tag`) depend on a
specific CRS value:

```
Msg : {secParam n : Nat} → Crs secParam n → Type
```

This way, the type-checker enforces arity agreement between `setup`,
`MAC`, and `verify`: a `Tag` produced from `crs : Crs secParam n` cannot
be passed to `verify` at a different arity, because the types literally
differ.

### Monad polymorphism

`AlgebraicMACSyntax` is parameterised by an abstract monad `M` with
`[Monad M]` so the same scheme value can be interpreted in multiple
randomness models:

- `M := Id` — deterministic interpretation (toy schemes, sanity checks).
- `M := ProbComp` — VCV-io's probabilistic-computation monad, used by
  game-based reductions in security tracks. The `Correct` predicate and
  the UF-CMVA game both fix `M := ProbComp`; the syntactic structure
  itself stays polymorphic.
- Future symbolic interpretations plug in a different `M` (e.g. a
  Dolev–Yao term-algebra monad).

### Decidable equality on message vectors

The UF-CMVA game's freshness check (`m* ∉ signedLog`) requires
decidable equality on the message-vector type `Fin n → mac.Msg crs`.
We surface that via a structure field `DecidableEqMsg` providing
`DecidableEq (Msg crs)` for every CRS; the vector form is then
derivable via `Pi.decidableEq` at use sites.
-/

namespace KVAC.Core

/--
Syntactic algebraic MAC per O24 Definition 3.1.

A value `mac : AlgebraicMACSyntax M` packages the four MAC algorithms
under an abstract monad `M`. Type families:

- `Crs secParam n` — common-reference-string type indexed by the security
  parameter and the attribute count.
- `Msg crs`, `Sk crs`, `Pp crs`, `Tag crs` — carrier types selected by
  the CRS.

Correctness and UF-CMVA security are *not* fields of this structure —
both are proved per scheme as standalone obligations in
`Correctness.lean` and `UFCMVA.lean`. Trade-off: lose the
by-construction guarantee of a bundled correctness field (cf. PQXDH's
`KEM`); gain monad polymorphism, since correctness statements differ in
shape between `Id` (Bool equation) and `ProbComp` (`support` / `evalDist`
form), and the two cannot share a single field signature.
-/
structure AlgebraicMACSyntax (M : Type → Type) [Monad M] where
  /-- Common-reference-string type, indexed by security parameter and
  attribute count. -/
  Crs : Nat → Nat → Type
  /-- Attribute (message) type, selected by the CRS. The MAC operates on
  `Fin n → Msg crs` (the paper's `m⃗ ∈ M_crs^n`). -/
  Msg : {secParam n : Nat} → Crs secParam n → Type
  /-- Secret-key type, selected by the CRS. -/
  Sk : {secParam n : Nat} → Crs secParam n → Type
  /-- Public-parameter type, selected by the CRS. -/
  Pp : {secParam n : Nat} → Crs secParam n → Type
  /-- MAC-tag type, selected by the CRS. -/
  Tag : {secParam n : Nat} → Crs secParam n → Type
  /-- Decidable equality on the message type. The UF-CMVA freshness check
  uses `DecidableEq (Fin n → Msg crs)`, which is derivable from this
  field via `Pi.decidableEq` (since `Fin n` is a `Fintype`). This is an
  implementation requirement for the Boolean UF-CMVA game, not a
  cryptographic assumption. -/
  DecidableEqMsg : {secParam n : Nat} → (crs : Crs secParam n) →
    DecidableEq (Msg crs)
  /-- Setup algorithm. Takes a security parameter `secParam` (the Lean
  rendering of O24's `1^λ` unary input) and attribute count `n`; returns
  a CRS in `M`. -/
  setup : (secParam n : Nat) → M (Crs secParam n)
  /-- Key generation. Takes a CRS and returns `(sk, pp)` in `M`. -/
  keygen : {secParam n : Nat} → (crs : Crs secParam n) →
    M (Sk crs × Pp crs)
  /-- MAC algorithm. Takes the secret key and an `n`-attribute vector,
  returns a tag in `M`. -/
  MAC : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    (Fin n → Msg crs) → M (Tag crs)
  /-- Verification algorithm. Deterministic per O24 §3.2 — does not enter
  the monad. -/
  verify : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    (Fin n → Msg crs) → Tag crs → Bool

/-- The `DecidableEqMsg` field promoted to a typeclass instance so that
downstream files can use `DecidableEq (mac.Msg crs)` without manual
projections. -/
instance (M : Type → Type) [Monad M] (mac : AlgebraicMACSyntax M)
    {secParam n : Nat} (crs : mac.Crs secParam n) :
    DecidableEq (mac.Msg crs) :=
  mac.DecidableEqMsg crs

/-- An `n`-attribute message vector under the CRS, matching O24's `m⃗ ∈ M^n`
notation. Used by `Correct`, the UF-CMVA game, and (later) the concrete
schemes μCMZ and μBBS. -/
abbrev MsgVec {M : Type → Type} [Monad M] (mac : AlgebraicMACSyntax M)
    {secParam n : Nat} (crs : mac.Crs secParam n) : Type :=
  Fin n → mac.Msg crs

end KVAC.Core
