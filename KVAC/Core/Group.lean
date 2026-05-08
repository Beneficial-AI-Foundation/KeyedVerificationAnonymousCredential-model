/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Prime-order group (Track 0)

Abstract typeclass for the prime-order group $\mathbb{G}$ used throughout
Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint
2024/1552 (§3.1). All higher-layer modules (`Preliminaries/`, `ProofSystems/`,
`Framework/`, `Schemes/`) are stated over this typeclass rather than a specific
curve.

Concrete instances live under `KVAC/Instances/` and are added when the
`Examples/` track lands — Ristretto255 (via
[`curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify))
for the μCMZ instance.

See `docs/PLAN.md` for the design intent.
-/

namespace KVAC.Core

-- TODO(Track 0): define the `PrimeOrderGroup` typeclass here.

end KVAC.Core
