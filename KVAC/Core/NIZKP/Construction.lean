/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/

/-!
# Non-interactive zero-knowledge proof — syntactic layer (O24 §3.3)

Syntactic part of a non-interactive proof system per Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552, §3.3.

The paper-level `NIZKP` object is layered like `AlgebraicMAC`:

- **`NIZKPSyntax M`** (this file) — the three algorithms S / P / V and the
  crs-indexed relation family, with no semantic obligations. Polymorphic in
  the randomness monad `M` (`Id`, `ProbComp`, future symbolic monads).
- **`PerfectlyComplete`** (in `Completeness.lean`) — completeness predicate on
  an `NIZKPSyntax ProbComp`, support-based.
- **Zero-knowledge** game + advantage (in `Security.lean`) — the two-world
  game of O24 §3.3 with a random oracle, opt-in.
- **`NIZKP`** (in the umbrella file `KVAC.Core.NIZKP`) — the paper-level
  object: an `NIZKPSyntax ProbComp` together with a proof of completeness.

## Design notes

### The object

O24 §3.3: a proof system ZKP for a relation family 𝓡 = {R_λ} is
crs ← ZKP.S(1^λ), π ← ZKP.P(crs, x, w), 0/1 ← ZKP.V(crs, x, π). The crs
implicitly selects a relation R ∈ 𝓡, so `relation`, `Stmt`, `Witness`, and
`Proof` are all indexed by the crs.

### Kinds of non-interactiveness

Three senses must not be conflated.

- **The proof is non-interactive.** The honest prover→verifier flow is a single
  message: P outputs π, V checks it, no challenge round. This is the NI of
  NIZKP, and it is why `prove` and `verify` are one-shot, not a multi-round
  exchange.
- **Fiat–Shamir provides it.** The μCMZ/μBBS instantiations are interactive
  Σ-protocols made non-interactive by computing the challenge as c = H(a, x)
  through the random oracle instead of receiving it from the verifier; the
  oracle replaces the interaction round.
- **The game's oracle access is not protocol interaction.** In `Security.lean`
  the adversary queries a `Prove` oracle (and, later, the random oracle); that
  models what an adversary may observe, not a round of the honest protocol, and
  does not make the scheme interactive.

### Verify is monadic

O24 writes 0/1 ← ZKP.V with a sampling arrow, unlike the deterministic
0/1 := MAC.V of §3.2. A Fiat–Shamir verifier recomputes the challenge
c = H(a, x) through the random oracle, so `verify` returns `M Bool`, not
`Bool`.

### Monad polymorphism

`NIZKPSyntax` is parameterised by an abstract monad `M` with `[Monad M]`, so
one scheme value interprets in several randomness models: `M := Id`
(deterministic sanity checks), `M := ProbComp` (game-based reasoning; the
completeness predicate and the zero-knowledge game both fix `M := ProbComp`).
The random oracle enters at the game boundary in `Security.lean`, not the scheme
carrier.
-/

namespace KVAC.Core

/--
Syntactic non-interactive proof system per O24 §3.3.

A value `zkp : NIZKPSyntax M` packages the three algorithms under an abstract
monad `M`. Type families selected by the crs:

- `Crs secParam` — common-reference-string type, indexed by the security
  parameter (O24's `1^λ`).
- `Stmt crs`, `Witness crs`, `Proof crs` — statement, witness, and proof
  types of the relation `crs` selects.

Completeness and zero-knowledge are *not* fields; they are proved per scheme
as standalone obligations in `Completeness.lean` and `Security.lean`, the
same trade-off as `AlgebraicMACSyntax`.
-/
structure NIZKPSyntax (M : Type → Type) [Monad M] where
  /-- Common-reference-string type, indexed by the security parameter. -/
  Crs : Nat → Type
  /-- Statement (instance) type, selected by the crs. -/
  Stmt : {secParam : Nat} → Crs secParam → Type
  /-- Witness type, selected by the crs. -/
  Witness : {secParam : Nat} → Crs secParam → Type
  /-- Proof type, selected by the crs. -/
  Proof : {secParam : Nat} → Crs secParam → Type
  /-- Setup `ZKP.S(1^λ)`. Takes the security parameter and returns a crs in
  `M`; the crs implicitly selects a relation R ∈ 𝓡. -/
  setup : (secParam : Nat) → M (Crs secParam)
  /-- Prover `ZKP.P(crs, x, w)`. From a witnessed instance produces a proof
  in `M`. -/
  prove : {secParam : Nat} → (crs : Crs secParam) →
    Stmt crs → Witness crs → M (Proof crs)
  /-- Verifier `ZKP.V(crs, x, π)`. Returns `true`/`false` in `M`; monadic
  because a Fiat–Shamir verifier queries the random oracle. -/
  verify : {secParam : Nat} → (crs : Crs secParam) →
    Stmt crs → Proof crs → M Bool
  /-- The relation `crs` selects: `relation crs x w` says `w` witnesses `x`
  (O24 §3.3, the crs-indexed R ∈ 𝓡). -/
  relation : {secParam : Nat} → (crs : Crs secParam) →
    Stmt crs → Witness crs → Prop

end KVAC.Core
