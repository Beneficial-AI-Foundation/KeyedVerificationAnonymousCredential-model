/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal


#doc (Manual) "Concrete run" =>
%%%
tag := "concrete_run"
%%%

A small evaluable Lean script exercising the *μCMZ* protocol end-to-end
against a verified Ristretto255 instance. The chapter covers both pieces
of Track Ex (the project's last Wave):

- `KVAC/Instances/Ristretto.lean` — the only place Ristretto255 appears.
  Local binding of the abstract `PrimeOrderGroup` and `SampleableGroup`
  typeclasses to the verified Ristretto255 instance from
  `curve25519-dalek-lean-verify`.
- `KVAC/Examples/ConcreteRun.lean` — the runnable example itself.

Track Ex bundles three changes into a single PR: this example file, the
`Instances/Ristretto.lean` binding, and the addition of
`curve25519-dalek-lean-verify` to `lakefile.toml`. Until Track Ex lands,
none of these files exists and the lakefile does not import dalek.

*Why not μBBS here?* μBBS requires a curve larger than Ristretto255
(at least 384-bit) for 128-bit security under q-DL — see the *μBBS*
chapter. A μBBS concrete run is deferred to post-v1.

# Ristretto255 instance

:::group "ex_instance"
The single concrete plug-in into the abstract typeclass stack:
`Ristretto255` is instantiated as a `PrimeOrderGroup` and a
`SampleableGroup` over `ZMod p` (for `p` the Ristretto group order). Two
import rules make the boundary enforceable: only `Examples/` and the
scheme-specific security tracks may import from `Instances/`; no other
directory may.
:::

*TODO (Track Ex).* Define the Ristretto instance binders in
`KVAC/Instances/Ristretto.lean`. Add the dalek Lake dependency to the
parent `lakefile.toml` in the same PR.

# End-to-end μCMZ run

:::group "ex_concrete_run"
A `decide` (or `native_decide`) sanity check exercising the μCMZ
protocol: instantiate the typeclasses against Ristretto, run a small
issuance and presentation, check the verifier accepts. The smoke test
catches abstraction mismatches between *Core*, *Framework*, and
*μCMZ*, and serves as documentation by example.
:::

*TODO (Track Ex).* Write the end-to-end example in
`KVAC/Examples/ConcreteRun.lean`. Aim for 50 to 100 lines of glue.

# Optional: μBBS over a larger curve

*Deferred to post-v1.* μBBS requires a roughly 300 to 384-bit curve (for
example the BLS12-381 base curve, used without pairings) for 128-bit
security under q-DL. A verified larger-curve instance is not yet
available; once one lands, a parallel μBBS example would mirror this
chapter.
