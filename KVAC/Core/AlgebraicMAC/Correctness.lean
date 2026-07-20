/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.AlgebraicMAC.Construction
import VCVio.OracleComp.ProbComp

/-!
# Correctness of an algebraic MAC (O24 Definition 3.1)

Correctness predicate `Correct` on an `AlgebraicMACSyntax ProbComp`:
every honestly produced tag verifies.

## Three equivalent formulations

For a "with probability 1" correctness claim in `ProbComp`, three
formulations are available:

1. **Support-based:** `∀ b ∈ support (do { ... }), b = true`. Lightest
   to prove (`simpa [scheme]` often suffices) and what we use here.
2. **`Pr[…]`-based:** `Pr[= true | do { ... }] = 1`. Equivalent to (1)
   for correctness; heavier to manipulate (PMF reasoning).
3. **`evalDist`-based:** `evalDist (do { ... }) = evalDist (pure true)`.
   Strongest formulation; only needed when the claim involves a
   non-trivial target distribution.

For correctness, all three are logically equivalent. We pick (1)
because its proofs reduce to `simp` on the scheme definition. Later
definitions that involve *exact* probability claims (advantages,
indistinguishability, distinguishing bounds) should reach for (2) or
(3) instead.

(Note: in a deterministic monad `M = Id`, correctness can also be
stated as the syntactic equation `(do { ... }) = pure true`, proved by
`rfl`. That form is not available in `ProbComp` because the free-monad
structure preserves sample / bind nodes — see `Construction.lean` for
the monad-polymorphism design notes.)

## Out of scope

The bundled paper-level object `AlgebraicMAC` (an
`AlgebraicMACSyntax ProbComp` paired with a `Correct` proof) is defined
in the umbrella file `KVAC/Core/AlgebraicMAC.lean`.
-/

namespace KVAC.Core

open OracleComp

/--
Correctness for an algebraic MAC (O24 Definition 3.1): for every CRS
in the support of `setup`, every key pair in the support of `keygen`,
every attribute vector, and every tag in the support of `MAC`, the
deterministic `verify` algorithm returns `true`.

Support-based form — see the module docstring for the four equivalent
formulations and why we chose this one.
-/
def Correct (mac : AlgebraicMACSyntax ProbComp) : Prop :=
  ∀ (secParam n : Nat),
  ∀ (crs : mac.Crs secParam n), crs ∈ support (mac.setup secParam n) →
  ∀ (keys : mac.Sk crs × mac.Pp crs), keys ∈ support (mac.keygen crs) →
  ∀ (m : mac.MsgVec crs),
  ∀ (sig : mac.Tag crs), sig ∈ support (mac.MAC crs keys.1 m) →
    mac.verify crs keys.1 m sig = true

end KVAC.Core
