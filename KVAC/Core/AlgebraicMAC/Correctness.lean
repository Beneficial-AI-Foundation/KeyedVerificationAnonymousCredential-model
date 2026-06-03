/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.AlgebraicMAC.Syntax
import VCVio.OracleComp.ProbComp

/-!
# Functional correctness of an algebraic MAC (O24 Definition 3.1)

Functional correctness predicate `Correct` on an
`AlgebraicMACSyntax ProbComp`: every honestly produced tag verifies.

## Four equivalent (for "with probability 1") formulations

For a probabilistic correctness claim like O24's, four formulations are
in principle available:

1. **Syntactic:** `(do { ... }) = (pure true : ProbComp Bool)`.
   *Not provable* in `ProbComp`: `ProbComp` is a free monad over a
   polynomial functor, so `bind ma (fun _ => pure b) ≠ pure b` as a
   `ProbComp` term, even when the two have identical distribution.
2. **Support-based:** `∀ b ∈ support (do { ... }), b = true`. Lightest
   to prove (`simpa [scheme]` often suffices) and what we use here.
3. **`Pr[…]`-based:** `Pr[= true | do { ... }] = 1`. Equivalent to (2)
   for correctness; heavier to manipulate (PMF reasoning).
4. **`evalDist`-based:** `evalDist (do { ... }) = evalDist (pure true)`.
   Strongest formulation; only needed when the claim involves a
   non-trivial target distribution.

For correctness, (2)/(3)/(4) are logically equivalent. We pick (2)
because its proofs reduce to `simp` on the scheme definition. Later
definitions that involve *exact* probability claims (advantages,
indistinguishability, distinguishing bounds) should reach for (3) or (4)
instead.

## Out of scope

The bundled paper-level object `AlgebraicMAC` (an
`AlgebraicMACSyntax ProbComp` paired with a `Correct` proof) is defined
in the umbrella file `KVAC/Core/AlgebraicMAC.lean`.
-/

namespace KVAC.Core

open OracleComp

/--
Functional correctness for an algebraic MAC (O24 Definition 3.1):
for every CRS in the support of `setup`, every key pair in the support
of `keygen`, every attribute vector, and every tag in the support of
`MAC`, the deterministic `verify` algorithm returns `true`.

Support-based form — see the module docstring for the four equivalent
formulations and why we chose this one.
-/
def Correct (mac : AlgebraicMACSyntax ProbComp) : Prop :=
  ∀ (secParam n : Nat),
  ∀ (crs : mac.Crs secParam n), crs ∈ support (mac.setup secParam n) →
  ∀ (keys : mac.Sk crs × mac.Pp crs), keys ∈ support (mac.keygen crs) →
  ∀ (m : MsgVec mac crs),
  ∀ (sig : mac.Tag crs), sig ∈ support (mac.MAC crs keys.1 m) →
    mac.verify crs keys.1 m sig = true

end KVAC.Core
