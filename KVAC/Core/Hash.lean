/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Hash and random-oracle interfaces (Track 0)

Abstract interfaces for the paper's hash functions: `HashToG`, `HashToZq`, and
`Derive` (CPZ19 §2.1, §6). For Phase 1 these are treated as opaque; for the
security phases (Phase 5) they are backed by VCV-io oracle semantics so that
random-oracle reductions can be expressed.

See `docs/PLAN.md` for the design intent.
-/

namespace KVAC.Core

-- TODO(Track 0): define the hash and random-oracle typeclasses here.

end KVAC.Core
