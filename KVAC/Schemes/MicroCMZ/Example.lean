/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.Construction
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# μCMZ base-MAC: a computable example over `ZMod p`

Demonstrates that the μCMZ base-MAC (O24 §5.1, Figure 9) is computable when
instantiated at a concrete prime-order group, once a *computable*
`SampleableType {g : ZMod (n + 1) // g ≠ 0}` instance is supplied.

## Why a separate file

The abstract `microCMZBaseMACSyntax` (in `Construction.lean`) and its helper
`uniformNonzero` are declared `noncomputable def`: they are stated over an
arbitrary `SampleableGroup F G`, and the generic `SampleableType` for an
arbitrary finite subtype is built on `Fintype.equivFin`, which is itself
`noncomputable` (it chooses a canonical ordering of the type via
`Classical.choice`).

For `G = ZMod (n + 1)` this obstruction disappears: `ZMod (n + 1)` is
*already* canonically indexed — it is definitionally `Fin (n + 1)` (so
`ZMod.finEquiv` is `.refl _`) — and the nonzero subtype
`{g : ZMod (n + 1) // g ≠ 0}` is in computable bijection with `Fin n` via
`finSuccAboveEquiv 0` (the map `i ↦ i + 1` shifts `Fin n` onto `{1, …, n}`).
Providing that instance directly, at higher priority than the generic one, lets
the concrete `microCMZBaseMACSyntaxZMod` below compile without `noncomputable`
and produce real compiled code (`lake env lean … -c` emits a 50 KB `.c` with the
function bodies, confirmed).

We parametrise by `n` (rather than the prime `p`) so that the `n + 1` is
syntactic and `finSuccAboveEquiv` type-checks directly; the group is then
`ZMod (n + 1)`, prime-order when `n + 1` is prime. The construction body below is
byte-for-byte the same algorithm as `microCMZBaseMACSyntax`; only the generality
(and hence the `noncomputable` marker) differs.

## Executing a run (known limitation)

`microCMZBaseMACSyntaxZMod` and `mac5` are computable *definitions*, but
driving an end-to-end `keygen`/`MAC` run at a concrete `crs := 0` literal
(e.g. via `#eval` on `simulateQ … demoComp`) is currently too expensive to
elaborate: `OfNat (mac5.Crs …) 0` unfolds the `Crs` projection to `ZMod 5` and
then chains through the high-priority `SampleableType {g : ZMod 5 // g ≠ 0}`
instance and `unifSpec`'s `OracleSpec`, which exceeds the heartbeat budget even
when raised. This is a Lean instance-search ergonomics issue at the call site,
*not* a computability obstruction — the function bodies themselves are compiled.
Resolving it (e.g. by locally lowering the nonzero-subtype instance priority at
the call site, or by giving `mac5` a reducible `abbrev` form) is left as a
follow-up.
-/

namespace KVAC.Schemes.MicroCMZ.Example

open KVAC.Core OracleComp

set_option autoImplicit false

/-- The bijection `Fin n ≃ {g : ZMod (n + 1) // g ≠ 0}`: `i ↦ i + 1` shifts
`Fin n` onto the nonzero elements `{1, …, n}` of `ZMod (n + 1)`. Built straight
from `finSuccAboveEquiv 0`, using that `ZMod (n + 1)` is definitionally
`Fin (n + 1)`. Computable. -/
def nonzeroZModEquiv (n : ℕ) :
    Fin n ≃ {g : ZMod (n + 1) // g ≠ 0} :=
  finSuccAboveEquiv (0 : ZMod (n + 1))

/-- A *computable* `SampleableType` for the nonzero elements of `ZMod (n + 1)`,
bypassing the generic `Fintype.equivFin`-based instance. Higher priority than the
generic `instSampleableTypeNeZero` so instance search prefers it here. -/
instance (priority := high) instSampleableTypeNeZeroZModSucc (n : ℕ) [NeZero n] :
    SampleableType {g : ZMod (n + 1) // g ≠ 0} :=
  SampleableType.ofEquiv (nonzeroZModEquiv n)

namespace ZModPMAC

variable (n : ℕ) [hn : NeZero n]

/-- Concrete computable `uniformNonzero` over `ZMod (n + 1)`: samples the nonzero
subtype via the computable instance above and projects away the `≠ 0` witness.
Unlike the abstract `uniformNonzero` this is a plain `def`. -/
def uniformNonzeroZMod : ProbComp (ZMod (n + 1)) := do
  let u ← ($ᵗ {g : ZMod (n + 1) // g ≠ 0} : ProbComp {g : ZMod (n + 1) // g ≠ 0})
  pure u.val

/-- μCMZ base-MAC over `ZMod (n + 1)`, as a computable syntactic algebraic MAC.
Same algorithm as `microCMZBaseMACSyntax`, specialized to
`F = G = ZMod (n + 1)` with the concrete generator `gen : ZMod (n + 1)`. -/
def microCMZBaseMACSyntaxZMod (gen : ZMod (n + 1)) :
    AlgebraicMACSyntax ProbComp where
  Crs := fun _ _ => ZMod (n + 1)
  Msg := fun _ => ZMod (n + 1)
  Sk := fun {_secParam m} _ => ZMod (n + 1) × ZMod (n + 1) × (Fin m → ZMod (n + 1))
  Pp := fun {_secParam m} _ => ZMod (n + 1) × ZMod (n + 1) × (Fin m → ZMod (n + 1))
  Tag := fun _ => ZMod (n + 1) × ZMod (n + 1)
  DecidableEqMsg := fun _ => inferInstance
  setup := fun _secParam _m => ($ᵗ ZMod (n + 1))
  keygen := fun {_secParam m} crs => do
    let x0 ← $ᵗ ZMod (n + 1)
    let xr ← $ᵗ ZMod (n + 1)
    let x ← $ᵗ (Fin m → ZMod (n + 1))
    pure ((x0, xr, x), (x0 • crs, xr • gen, fun i => x i • gen))
  MAC := fun {_secParam _m} _crs sk msg => do
    let U ← uniformNonzeroZMod n
    pure (U, (sk.1 + sk.2.1 + ∑ i, msg i * sk.2.2 i) • U)
  verify := fun {_secParam _m} _crs sk msg t =>
    decide (t.1 ≠ 0) && decide (t.2 = (sk.1 + sk.2.1 + ∑ i, msg i * sk.2.2 i) • t.1)

end ZModPMAC

/-- The concrete MAC at `n = 4` (so `G = ZMod 5`, prime order), generator
`gen = 1`. -/
def mac5 : AlgebraicMACSyntax ProbComp := ZModPMAC.microCMZBaseMACSyntaxZMod 4 1

end KVAC.Schemes.MicroCMZ.Example

