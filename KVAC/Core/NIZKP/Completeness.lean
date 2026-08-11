/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Security
import VCVio.OracleComp.ProbComp

/-!
# Completeness of a non-interactive proof system (O24 §3.3)

Completeness predicate `PerfectlyComplete` on an
`NIZKPSyntax (OracleComp (ZKRO H))`: "every correctly-generated proof for an
element of R verifies" (O24 §3.3).

Perfect completeness is the support-based form: for an honestly generated crs
and a witnessed instance, every honestly produced proof makes `verify` accept
with certainty, i.e. `true` is the only value in the support of `verify`. This
mirrors `Correct` in `AlgebraicMAC/Correctness.lean`; see that file for why
the support-based form is chosen over the `Pr[…]` and `evalDist` forms.

Because the scheme lives at the carrier `OracleComp (ZKRO H)`, `setup`, `prove`,
and `verify` are interpreted through `zkROImpl` on one shared cache, threaded
`∅ → c₀ → c₁`, so a Fiat–Shamir `verify` sees the very oracle answers its
`prove` produced.

A completeness *error* would relax this to a bound on `Pr[= false | verify …]`;
we state the perfect notion first.
-/

namespace KVAC.Core

open OracleComp OracleSpec

/--
Perfect completeness (O24 §3.3, p.25): "A proof system is complete if every
correctly-generated proof for an element of R verifies."

Formally: for every crs and cache in the support of the interpreted `setup`,
every witnessed instance `relation crs x w`, and every proof `π` and cache in
the support of the interpreted `prove crs x w` on that cache, the interpreted
`verify crs x π` on the resulting cache returns `true` with certainty — no
`false` is possible.
-/
def PerfectlyComplete (H : HashSpec) (zkp : NIZKPSyntax (OracleComp (ZKRO H))) : Prop :=
  ∀ (secParam : Nat),
  ∀ (crs : zkp.Crs secParam) (c₀ : H.Cache),
    (crs, c₀) ∈ support ((simulateQ (zkROImpl H) (zkp.setup secParam)).run ∅) →
  ∀ (x : zkp.Stmt crs) (w : zkp.Witness crs), zkp.relation crs x w →
  ∀ (π : zkp.Proof crs) (c₁ : H.Cache),
    (π, c₁) ∈ support ((simulateQ (zkROImpl H) (zkp.prove crs x w)).run c₀) →
  ∀ (b : Bool) (c₂ : H.Cache),
    (b, c₂) ∈ support ((simulateQ (zkROImpl H) (zkp.verify crs x π)).run c₁) → b = true

end KVAC.Core
