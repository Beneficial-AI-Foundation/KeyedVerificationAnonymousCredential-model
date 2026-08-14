/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Framework.Syntax
import KVAC.Framework.Correctness

/-!
# Keyed-verification credential systems (O24 Definition 4.2)

Defines the paper-level bundled object `KVAC` per Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552,
Definition 4.2: a `KVACSyntax ProbComp` paired with a proof of correctness
(Definition 4.3).

Re-exports `Syntax.lean` (the syntactic structure) and `Correctness.lean`
(the correctness predicate) — i.e. what the bundle is built from. The
anonymity game (`Anonymity.lean`) and extractability game
(`Extractability.lean`) are *not* re-exported, matching `AlgebraicMAC`:
they are not part of the paper-level definition, and files reasoning about
those properties import `KVAC.Framework.Anonymity` /
`KVAC.Framework.Extractability` explicitly.

## Layering recap

```
                   Framework.lean (this file — bundle)
                           │
                ┌──────────┴──────────┐
                ▼                     ▼
           Syntax.lean          Correctness.lean
                                      │
                                      └── (used by Correct predicate)

     Anonymity.lean / Extractability.lean (security games, opt-in)
```

- `Syntax.lean` — `KVACSyntax M` (Definitions 4.1, 4.2), polymorphic over
  the randomness monad.
- `Correctness.lean` — `Correct` predicate, support-based (Definition 4.3).
- `Anonymity.lean` — anonymity game + advantage (Definition 4.4), opt-in.
- `Extractability.lean` — extractability game (Definition 4.5, Figure 8),
  opt-in.
- This file — `KVAC`, the bundled paper-level object.

The paper's Definition 4.2 closes with "a keyed-verification credential
system satisfies correctness, anonymity, and unforgeability"; as with the
MAC layer, only correctness enters the bundle (it is a plain `Prop` with a
canonical statement), while anonymity and extractability are quantitative
games kept as standalone predicates/advantages for the security theorems
to bound.

The bundle fixes `M := ProbComp` because correctness is distributional. The
syntactic layer stays monad-polymorphic to leave room for symbolic
interpretations.
-/

namespace KVAC.Framework

/--
Paper-level keyed-verification credential system per O24 Definition 4.2:
a syntactic credential system over `ProbComp` paired with a proof of
correctness (Definition 4.3).
-/
structure KVAC where
  /-- The syntactic algorithms (S / K / I / P), with randomness fixed to
  `ProbComp`. -/
  alg : KVACSyntax ProbComp
  /-- Correctness of the syntactic algorithms (O24 Definition 4.3). -/
  correct : Correct alg

end KVAC.Framework
