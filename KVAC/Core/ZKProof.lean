/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP

/-!
# Zero-knowledge proofs (umbrella)

Aggregates the zero-knowledge proof modules. Currently:

- `KVAC.Core.NIZKP` — the paper-faithful non-interactive proof system (O24 §3.3):
  syntax (`Construction.lean`) and completeness (`Completeness.lean`).

The security-model-agnostic specification `KVAC.Core.NIZKP.Basic` is set aside per
`docs/NIZKP_PAPER_FAITHFUL_STRATEGY.md` and is no longer imported from the root.
Its revisit is tracked in issue #43.

Additional ZK modules are imported here as they are added.
-/
