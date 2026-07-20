/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Core.Group
import KVAC.Core.Hash
import KVAC.Core.ZKProof
import KVAC.Core.AlgebraicMAC

open Verso.Genre Manual
open Informal


#doc (Manual) "Core" =>
%%%
tag := "core"
%%%

Shared abstract algebra (Track 0). These typeclasses define the API contract
that every higher chapter imports: a prime-order group, hash and
random-oracle interfaces, a generic NIZK proof system, and the algebraic
MAC syntax of O24, Section 3.2. The interfaces are designed once and
remain stable across the life of the project; concrete instantiations
live in the *Concrete run* chapter.

Per `docs/PLAN.md`, `KVAC/Core/` may import VCV-io (for the project-wide
`SampleableType` convention) but must not depend on any
deployment-specific structure.

# Prime-order group

:::group "core_group"
The algebraic backbone: an abelian, finite, cyclic, simple group `G` with
scalars in a generic field `F`. Equivalent — for a finite abelian group —
to `G ≃ ZMod p` for a prime `p`. Together with the `Module F G` action,
this is the abstract setting of O24, Section 3.1.

Two `class abbrev`s bundle the convention. Non-game files use the lighter
`PrimeOrderGroup`; game-construction files use `SampleableGroup`, which
extends it with VCV-io's `SampleableType G` for the `$ᵗ` sampling
notation.
:::

:::definition "prime_order_group" (lean := "KVAC.Core.PrimeOrderGroup") (parent := "core_group")
The base algebraic convention: an `AddCommGroup G` that is `Fintype`,
`IsAddCyclic`, and `IsSimpleAddGroup`, together with a `Module F G`
action over a generic field `F`. Sufficient for abstract-syntax and
correctness files that do not sample group elements.
:::

:::definition "sampleable_group" (lean := "KVAC.Core.SampleableGroup") (parent := "core_group")
A `PrimeOrderGroup F G` plus `SampleableType G`, intended for
security-game files that need VCV-io sampling on the group. Requires the
F-side `Fintype`, `DecidableEq`, `SampleableType` binders, and
`DecidableEq G` at the call site (see the docstring for the canonical
variable block).
:::

The notation convention is *additive* throughout, matching O24, Section
3.1 — the paper's `xG = X` becomes `x • G₀ = X` in Lean. See
`docs/STYLE_GUIDE.md` for the project-wide rule.

# Hash and random-oracle interfaces

:::group "core_hash"
Abstract interface for the two hash functions of O24, both modelled as
random oracles: a transcript hash `H_p` mapping bit-strings to `ZMod p`
(used in Fiat–Shamir), and a hash-to-curve `H_G` mapping bit-strings to
group elements. `HashSpec` packages a hash's domain and range with the
instances a random-oracle implementation needs; `HashSpec.spec` is the
induced VCV-io `OracleSpec` signature `Dom →ₒ Rng`, and `HashSpec.roImpl`
binds it to VCV-io's lazy caching `randomOracle` over a `QueryCache`.
`transcriptHashSpec` and `curveHashSpec` name the paper's two
instantiations. Domains stay abstract (structured per scheme); the
injective-encoding and domain-separation obligations of the paper's
`{0,1}*` domain are discharged at the instantiation layer.
:::

# Generic NIZK proof system

:::group "core_zkproof"
A non-interactive zero-knowledge proof system `ZKP = (S, P, V)` over a
relation family `R`. Setup yields a CRS; the prover takes `(crs, x, w)`
with `(x, w)` in `R`; the verifier checks a proof `π`. The four security
properties are completeness, knowledge soundness, zero-knowledge, and
(optionally) simulation-extractability — knowledge soundness under access
to simulated proofs.
:::

*TODO (Track 0).* Define the proof-system typeclass and the four
security predicates, mirroring O24 Section 3.3.

# Algebraic MAC

:::group "core_amac"
The syntax of O24 Section 3.2, Definition 3.1: an algebraic MAC
`MAC = (S, K, M, V)` for `n` attributes over a message family, with
correctness (every honestly generated MAC verifies) and UF-CMVA
(unforgeability under chosen-message and verification attacks) as the
target security notion. The abstract framework's extractability chapter
then proves the bridge from MAC UF-CMVA to KVAC extractability.
:::

*TODO (Track 0).* Define the algebraic-MAC typeclass and the UF-CMVA
security game, mirroring Definition 3.1 and Figure 5 of O24.
