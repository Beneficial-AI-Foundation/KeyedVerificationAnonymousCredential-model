/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Construction
import VCVio.OracleComp.ProbComp

/-!
# Completeness of a non-interactive proof system (O24 §3.3)

Completeness predicate `PerfectlyComplete` on an `NIZKPSyntax ProbComp`:
"every correctly-generated proof for an element of R verifies" (O24 §3.3).

Perfect completeness is the support-based form: for an honestly generated crs
and a witnessed instance, every honestly produced proof makes `verify` accept
with certainty, i.e. `true` is the only value in the support of `verify`. This
mirrors `Correct` in `AlgebraicMAC/Correctness.lean`; see that file for why
the support-based form is chosen over the `Pr[…]` and `evalDist` forms.

A completeness *error* would relax this to a bound on `Pr[= false | verify …]`;
we state the perfect notion first.
-/

namespace KVAC.Core

open OracleComp

/--
Perfect completeness (O24 §3.3, p.25): "A proof system is complete if every
correctly-generated proof for an element of R verifies."

Formally: for every crs in the support of `setup`, every witnessed instance
`relation crs x w`, and every proof `π` in the support of `prove crs x w`,
`verify crs x π` returns `true` with certainty — no `false` is possible.
-/
def PerfectlyComplete (zkp : NIZKPSyntax ProbComp) : Prop :=
  ∀ (secParam : Nat),
  ∀ (crs : zkp.Crs secParam), crs ∈ support (zkp.setup secParam) →
  ∀ (x : zkp.Stmt crs) (w : zkp.Witness crs), zkp.relation crs x w →
  ∀ (π : zkp.Proof crs), π ∈ support (zkp.prove crs x w) →
  ∀ (b : Bool), b ∈ support (zkp.verify crs x π) → b = true

end KVAC.Core
