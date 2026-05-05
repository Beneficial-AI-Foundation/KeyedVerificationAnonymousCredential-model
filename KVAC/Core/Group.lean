/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Prime-order group (Track 0)

Abstract typeclass for the prime-order group $\mathbb{G}$ used throughout the
protocol of Chase, Perrin and Zaverucha (IACR ePrint 2019/1416). All higher-
layer modules (`Poksho/`, `ZkCredential/`, `ZkGroup/`, `Security/`) are stated
over this typeclass rather than a specific curve.

Concrete instances (axiomatized initially; eventually the verified Ristretto255
from [`curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify))
live in separate files and are swapped in via Lake without source changes
downstream.

See `docs/PLAN.md` for the design intent.
-/

namespace KVAC.Core

-- TODO(Track 0): define the `PrimeOrderGroup` typeclass here.

end KVAC.Core
