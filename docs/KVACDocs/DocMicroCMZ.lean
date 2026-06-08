/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal


#doc (Manual) "μCMZ" =>
%%%
tag := "microcmz"
%%%

The first concrete instantiation of the abstract framework, corresponding
to O24, Section 5. μCMZ improves on Chase–Meiklejohn–Zaverucha (2014):
O(1) issuance cost (down from O(n)), statistical anonymity, and security
in the algebraic group model under 3-DL. Deployed by Signal, Tor, and
NYM.

Five files under `KVAC/Schemes/MicroCMZ/`:

- `Construction.lean` — Section 5.1 — Track CMZ-C.
- `AlgebraicMAC.lean` — Section 5.3 — Track CMZ-M.
- `Anonymity.lean` — Section 5.4 — Track CMZ-A.
- `Extractability.lean` — Section 5.5 — Track CMZ-E.
- `OneMoreUnforgeability.lean` — Section 5.6 — Track CMZ-OMUF.

# Construction (Section 5.1)

:::group "cmz_construction"
The four protocol algorithms: `KeyGen`, `Setup`, `Issue` (with predicate
`φ`), and `Present`. Stated over the abstract `PrimeOrderGroup F G` —
no curve, hash function, or deployment is committed to here.
:::

*TODO (Track CMZ-C).* Implement the four algorithms following Section
5.1. Use the variable block from the style guide:

```
variable {F G : Type} [Field F] [PrimeOrderGroup F G]
```

# Algebraic-MAC security (Section 5.3)

:::group "cmz_amac"
*Theorem 5.1.* μCMZ, viewed as an algebraic MAC under the *Core*
algebraic-MAC interface, is UF-CMVA in the algebraic group model under
3-DL. The proof factors through two lemmas:

- *Lemma 5.4* — the `n = 1` attribute case,
- *Lemma 5.5* — the general `n`-attribute case, lifted from Lemma 5.4.

This is the load-bearing security result for μCMZ; both extractability
(Section 5.5) and the anonymous-token one-more unforgeability (Section
5.6) factor through it.
:::

*TODO (Track CMZ-M).* State Lemmas 5.4 and 5.5 and Theorem 5.1. Proofs
use AGM straight-line extraction from the *Proof systems* chapter.

# Anonymity (Section 5.4)

:::group "cmz_anonymity"
*Theorem 5.8.* μCMZ is anonymous (in the sense of *Framework*
anonymity) given a knowledge-sound ZK proof system. The
statistical-anonymity variant follows because μCMZ uses honest-verifier
zero-knowledge presentations with statistically indistinguishable
simulators.
:::

*TODO (Track CMZ-A).* State and prove Theorem 5.8. Use the
`SampleableGroup` typeclass (the game-construction variant of the
prime-order-group typeclass).

# Extractability (Section 5.5)

:::group "cmz_extract"
*Theorem 5.2.* μCMZ is extractable (in the sense of *Framework*
extractability) in the algebraic group model. The proof uses
straight-line extraction from the *Proof systems* chapter plus Theorem
5.1.
:::

*TODO (Track CMZ-E).* State and prove Theorem 5.2. The two key
ingredients are AGM straight-line extraction and the MAC unforgeability
result of Theorem 5.1.

# One-more unforgeability (Section 5.6)

:::group "cmz_omuf"
*Theorem 5.3.* The anonymous-token variant `μCMZ_AT` is one-more
unforgeable in the algebraic group model under 2-DL. `μCMZ_AT` is the
zero-attribute specialisation of μCMZ, providing only an
anonymous-token binding.
:::

*TODO (Track CMZ-OMUF).* State and prove Theorem 5.3 against the OMUF
game from the *Preliminaries* chapter.
