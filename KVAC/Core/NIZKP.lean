/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Construction
import KVAC.Core.NIZKP.Completeness

/-!
# Non-interactive zero-knowledge proof (O24 §3.3)

The paper-level bundled object `NIZKP` per Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §3.3: an `NIZKPSyntax ProbComp`
paired with a proof of completeness.

Re-exports `Construction.lean` (the syntactic structure) and `Completeness.lean`
(the completeness predicate). The zero-knowledge game (`Security.lean`) is *not*
re-exported, matching `AlgebraicMAC`: it is not part of the paper-level
definition, and files reasoning about zero-knowledge import
`KVAC.Core.NIZKP.Security` explicitly.

The bundle fixes `M := ProbComp` because completeness is distributional. The
syntactic layer stays monad-polymorphic to leave room for symbolic
interpretations.
-/

namespace KVAC.Core

/--
Paper-level non-interactive proof system per O24 §3.3: a syntactic proof
system over `ProbComp` paired with a proof of completeness.
-/
structure NIZKP where
  /-- The syntactic algorithms (Setup / Prove / Verify) and relation, with
  randomness fixed to `ProbComp`. -/
  alg : NIZKPSyntax ProbComp
  /-- Perfect completeness — every honestly produced proof verifies. -/
  complete : PerfectlyComplete alg

end KVAC.Core
