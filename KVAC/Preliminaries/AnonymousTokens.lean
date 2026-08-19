/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Preliminaries.AnonymousTokens.Construction
import KVAC.Preliminaries.AnonymousTokens.Correctness

/-!
# Anonymous tokens (O24 §3.4)

Defines the paper-level bundled object `AnonymousToken` per Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint
2024/1552 (O24), §3.4: an `ATSyntax ProbComp` paired with a proof of
correctness. The μCMZ_AT and μBBS_AT scheme variants (O24 Theorems
5.3 / 6.7, via Theorem 5.11 / Lemma 6.12) instantiate this interface.

Re-exports `Construction.lean` (the syntactic structure) and
`Correctness.lean` (the correctness predicate) — what the bundle is built
from. The one-more unforgeability game (`Security.lean`) is *not*
re-exported, matching `KVAC.Core.AlgebraicMAC`: it is a quantitative game
for the security theorems to bound, and files reasoning about OMUF import
`KVAC.Preliminaries.AnonymousTokens.Security` explicitly.

## Layering recap

- `Construction.lean` — `ATSyntax M` (§3.4's `AT = (S, K, I, V)`),
  polymorphic over the randomness monad, extending `KeyedSetupSyntax`.
- `Correctness.lean` — `Correct` predicate, support-based.
- `Security.lean` — the Figure 6 OMUF game and advantage, opt-in.
- This file — `AnonymousToken`, the bundled paper-level object.

§3.4 demands anonymous tokens be correct, one-more unforgeable, *and
unlinkable*, but omits unlinkability's formal definition
(keyed-verification token systems satisfy the stronger §4 anonymity
notions instead, and the paper defers the definition to
[KLOR20] / [DVC22]). We likewise do not formalize it; the blueprint node
records the gap. As with the MAC and KVAC layers, only correctness enters
the bundle, while OMUF stays a standalone game.
-/

namespace KVAC.Preliminaries

/--
Paper-level anonymous-token scheme per O24 §3.4: a syntactic scheme over
`ProbComp` paired with a proof of correctness, matching the bundling of
`KVAC.Core.AlgebraicMAC` and `KVAC.Framework.KVAC`. One-more
unforgeability stays a standalone quantitative game
(`KVAC.Preliminaries.AnonymousTokens.Security`), and unlinkability is not
formalized — see the module docstring.
-/
structure AnonymousToken where
  /-- The syntactic algorithms (S / K / I / V), with randomness fixed to
  `ProbComp`. -/
  alg : ATSyntax ProbComp
  /-- Correctness of the syntactic algorithms — every honestly issued
  token verifies. -/
  correct : alg.Correct

end KVAC.Preliminaries
