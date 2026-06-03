/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.AlgebraicMAC.Syntax
import KVAC.Core.AlgebraicMAC.Correctness

/-!
# Algebraic message authentication codes (O24 Definition 3.1)

Defines the paper-level bundled object `AlgebraicMAC` per Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint
2024/1552 Definition 3.1: an `AlgebraicMACSyntax ProbComp` paired with
a proof of functional correctness.

Re-exports `Syntax.lean` (the syntactic structure) and `Correctness.lean`
(the correctness predicate) — i.e. what the bundle is built from.
The UF-CMVA security predicate (`UFCMVA.lean`) is *not* re-exported
because it is not part of the paper-level definition of an algebraic
MAC; files that reason about UF-CMVA security import
`KVAC.Core.AlgebraicMAC.UFCMVA` explicitly.

## Layering recap

```
                   AlgebraicMAC.lean (this file — bundle)
                           │
                ┌──────────┴──────────┐
                ▼                     ▼
           Syntax.lean         Correctness.lean
                                      │
                                      └── (used by Correct predicate)

                   UFCMVA.lean (security predicate, opt-in)
                           │
                           └── imports Syntax only
```

- `Syntax.lean` — `AlgebraicMACSyntax M` (polymorphic over the
  randomness monad).
- `Correctness.lean` — `Correct (mac : AlgebraicMACSyntax ProbComp)`
  predicate, support-based.
- `UFCMVA.lean` — UF-CMVA game + advantage on
  `AlgebraicMACSyntax ProbComp`. Imported opt-in by files that need
  security reasoning, not transitively by this umbrella.
- This file — `AlgebraicMAC`, the bundled paper-level object.

The paper-level bundle commits to `M := ProbComp` because correctness
and security predicates are inherently distributional (free-monad
syntactic equality fails for `ProbComp`, so `Correct` cannot be stated
uniformly in `M`). The syntactic layer remains polymorphic to leave
room for future symbolic interpretations.
-/

namespace KVAC.Core

/--
Paper-level algebraic MAC per O24 Definition 3.1: a syntactic algebraic
MAC over `ProbComp` paired with a proof of functional correctness.
-/
structure AlgebraicMAC where
  /-- The syntactic algorithms (Setup / KeyGen / MAC / Verify), with
  randomness fixed to `ProbComp`. -/
  alg : AlgebraicMACSyntax ProbComp
  /-- Functional correctness of the syntactic algorithms — every
  honestly produced tag verifies. -/
  correct : Correct alg

end KVAC.Core
