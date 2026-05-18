/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Hash and random-oracle interfaces (Track 0)

Abstract interfaces for the hash functions used by Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552:
$H_p : \{0,1\}^* \to \mathbb{Z}_p$ for Fiat–Shamir transcripts and
$H_\mathbb{G} : \{0,1\}^* \to \mathbb{G}$ for hash-to-curve. VCV-io is a
Wave-0 Lake dependency, so these interfaces may either be stated abstractly or
expressed directly in terms of VCV-io's `OracleSpec` / `OracleComp` types
(decided when issue `#19` lands).

See `docs/PLAN.md` for the design intent.
-/

namespace KVAC.Core

-- TODO(Track 0): define the hash and random-oracle typeclasses here.

end KVAC.Core
