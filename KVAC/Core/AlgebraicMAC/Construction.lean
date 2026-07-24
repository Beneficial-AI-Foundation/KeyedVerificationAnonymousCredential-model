/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.KeyedSetup

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
- **`Correct`** (in `Correctness.lean`) — correctness predicate on an
  `AlgebraicMACSyntax ProbComp`, stated as a support-based equation.
- **UF-CMVA** game + advantage (in `Security.lean`) — security predicate
  on an `AlgebraicMACSyntax ProbComp`, in line with O24 Figure 5.
- **`AlgebraicMAC`** (in `KVAC.Core.AlgebraicMAC`, the umbrella file) —
  the paper-level object: an `AlgebraicMACSyntax ProbComp` together with
  a proof of `Correct`.

Splitting syntax / correctness / security into separate files follows the
convention requested in PR #24 review (separate file per security
property, e.g. as in the `proof-ladders` repo), so that concrete schemes
can import only what they need.

## Design notes

The CRS, message space, and `setup`/`keygen` come from `KeyedSetupSyntax`
(`KVAC.Core.KeyedSetup`) — see there for the intrinsic-typing and
monad-polymorphism discipline. This file adds only the MAC-specific carrier
`Tag` and the `MAC`/`verify` algorithms.
-/

namespace KVAC.Core

/--
Syntactic algebraic MAC per O24 Definition 3.1.

A value `mac : AlgebraicMACSyntax M` extends `KeyedSetupSyntax M` (the CRS,
message space, and `setup`/`keygen`) with the MAC-specific carrier `Tag` and
the `MAC` / `verify` algorithms, all under an abstract monad `M`.

Correctness and UF-CMVA security are *not* fields of this structure —
both are proved per scheme as standalone obligations in
`Correctness.lean` and `UFCMVA.lean`. Trade-off: lose the
by-construction guarantee of a bundled correctness field (cf. PQXDH's
`KEM`); gain monad polymorphism, since correctness statements differ in
shape between `Id` (Bool equation) and `ProbComp` (`support` / `evalDist`
form), and the two cannot share a single field signature.
-/
structure AlgebraicMACSyntax (M : Type → Type) [Monad M]
    extends KeyedSetupSyntax M where
  /-- MAC-tag type, selected by the CRS. -/
  Tag : {secParam n : Nat} → Crs secParam n → Type
  /-- MAC algorithm. Takes the secret key and an `n`-attribute vector,
  returns a tag in `M`. -/
  MAC : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    (Fin n → Msg crs) → M (Tag crs)
  /-- Verification algorithm. Deterministic per O24 §3.2 — does not enter
  the monad. -/
  verify : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
    (Fin n → Msg crs) → Tag crs → Bool

end KVAC.Core
