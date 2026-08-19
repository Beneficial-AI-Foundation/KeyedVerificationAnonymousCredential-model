/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Core.Group
import KVAC.Core.Hash
import KVAC.Core.ZKProof
import KVAC.Core.NIZKP.Security
import KVAC.Core.NIZKP.Extraction
import KVAC.Core.AlgebraicMAC
import KVAC.Core.AlgebraicMAC.Security

open Verso.Genre Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true


#doc (Manual) "Core" =>
%%%
tag := "core"
%%%

Shared abstract algebra (Track 0). These typeclasses define the API contract
that every higher chapter imports: a prime-order group, hash and
random-oracle interfaces, a generic NIZK proof system, the CRS and
key-generation skeleton shared by every keyed scheme, and the algebraic
MAC syntax of O24, Section 3.2. The interfaces are designed once and
remain stable across the life of the project; concrete instantiations
live in the *Concrete run* chapter.

Per `docs/PLAN.md`, `KVAC/Core/` may import VCV-io (for the project-wide
`SampleableType` convention) but must not depend on any
deployment-specific structure.

# Prime-order group

:::group "core_group"
Prime-order group
:::

The algebraic backbone: an abelian, finite, cyclic, simple group `G` with
scalars in a generic field `F`. Equivalent — for a finite abelian group —
to `G ≃ ZMod p` for a prime `p`. Together with the `Module F G` action,
this is the abstract setting of O24, Section 3.1.

Two `class abbrev`s bundle the convention. Non-game files use the lighter
`PrimeOrderGroup`; game-construction files use `SampleableGroup`, which
extends it with VCV-io's `SampleableType G` for the `$ᵗ` sampling
notation.

:::definition "prime_order_group" (lean := "KVAC.Core.PrimeOrderGroup") (parent := "core_group")
The base algebraic convention: an `AddCommGroup G` that is `Fintype`,
`IsAddCyclic`, and `IsSimpleAddGroup`, together with a `Module F G`
action over a generic field `F`. Sufficient for abstract-syntax and
correctness files that do not sample group elements.
:::

:::definition "sampleable_group" (lean := "KVAC.Core.SampleableGroup, KVAC.Core.SampleableType.ofNonemptySubtype") (parent := "core_group")
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
Hash and random-oracle interfaces
:::

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

:::definition "random_oracle_hashes" (lean := "KVAC.Core.HashSpec, KVAC.Core.HashSpec.spec, KVAC.Core.HashSpec.Cache, KVAC.Core.HashSpec.roImpl, KVAC.Core.HashSpec.transcriptHashSpec, KVAC.Core.HashSpec.curveHashSpec") (parent := "core_hash") (tags := "paper, O24 §3")
*O24 Section 3, Notation.* The two random-oracle hashes used throughout
the paper: `H_p : {0,1}* → ℤ_p` for Fiat–Shamir transcript hashing and
`H_G : {0,1}* → 𝔾` for hash-to-curve.
:::

# Generic NIZK proof system

:::group "core_zkproof"
Generic NIZK proof system
:::

A non-interactive zero-knowledge proof system `ZKP = (S, P, V)` over a
relation family `R`. Setup yields a CRS; the prover takes `(crs, x, w)`
with `(x, w)` in `R`; the verifier checks a proof `π`. The four security
properties are completeness, knowledge soundness, zero-knowledge, and
(optionally) simulation-extractability — knowledge soundness under access
to simulated proofs.

:::definition "nizkp_syntax" (lean := "KVAC.Core.NIZKPSyntax, KVAC.Core.NIZKP, KVAC.Core.PerfectlyComplete, KVAC.Core.NIZKPSyntax.DecidableRelation") (parent := "core_zkproof") (tags := "milestone")
The paper-faithful proof-system carrier of O24 Section 3.3: crs-indexed
statement, witness, and proof families with monad-polymorphic `setup`,
`prove`, and `verify`, the perfect-completeness predicate, decidability
of the relation family, and the syntax-plus-completeness bundle.
:::

:::definition "zk_game" (lean := "KVAC.Core.ZKQuery, KVAC.Core.ZKProveSpec, KVAC.Core.ZKRO, KVAC.Core.ZKAdvSpec, KVAC.Core.ZKAdversary, KVAC.Core.ZKSimulator, KVAC.Core.zkROImpl, KVAC.Core.zkProveReal, KVAC.Core.zkProveSim, KVAC.Core.zkRun, KVAC.Core.zkGameReal, KVAC.Core.zkGameSim, KVAC.Core.ZKAdv, KVAC.Core.runRO") (parent := "core_zkproof") (tags := "milestone")
The two-world zero-knowledge game of O24 Section 3.3 on a
{uses "nizkp_syntax"}[] carrier: a Proveᵦ oracle answering with the real
prover or the simulator behind the `(x, w) ∈ R` guard, the lazy random
oracle of {uses "random_oracle_hashes"}[] with a reprogrammable cache,
and the distinguishing advantage `ZKAdv`.
:::

:::definition "extraction_game" (lean := "KVAC.Core.NIZKPSyntax.DecidableEqStmt, KVAC.Core.NIZKPSyntax.DecidableEqProof, KVAC.Core.witnessValid, KVAC.Core.KSNDAdversary, KVAC.Core.KSNDExtractor, KVAC.Core.ksndGame, KVAC.Core.KSNDAdv, KVAC.Core.SEQuery, KVAC.Core.SESpec, KVAC.Core.SEAdvSpec, KVAC.Core.SEAdversary, KVAC.Core.SimLog, KVAC.Core.SEState, KVAC.Core.seOracleImpl, KVAC.Core.SEExtractor, KVAC.Core.seGame, KVAC.Core.SEAdv") (parent := "core_zkproof") (tags := "milestone")
The knowledge-soundness and strong simulation-extractability games of O24
Section 3.3 on a {uses "nizkp_syntax"}[] carrier at `OracleComp (ZKRO H)`,
building on the simulator and random oracle of {uses "zk_game"}[]:
white-box extractors receiving the adversary value and the run's
observables (the output pair, the random-oracle cache at the end of the
adversary's run, and for SE the simulation log), the two experiments
`ksndGame` and `seGame` with `verify` threaded through that cache, and the
advantages `KSNDAdv` and `SEAdv`. The SE extractor returns a candidate
statement (O24 Section 3.3, p. 25). The `verify` no-sampling constraint is
deferred (issue #101).
:::

# Keyed setup

:::group "core_keyed_setup"
Keyed setup
:::

A Lean-level factoring rather than an O24 object. The algebraic MAC of
Definition 3.1 and the keyed-verification credential system of
Definition 4.2 open the same way, sampling a CRS `crs ← S(1^λ, n)` and
then a key pair `(sk, pp) ← K(crs)` over a CRS-selected message space.
`KeyedSetupSyntax` carries that shared preamble, so the intrinsic-typing
discipline is stated once instead of being repeated. `AlgebraicMACSyntax`
extends it directly; the framework's `KVACSyntax` extends it through the
credential predicate family.

:::definition "keyed_setup" (lean := "KVAC.Core.KeyedSetupSyntax, KVAC.Core.KeyedSetupSyntax.MsgVec, KVAC.Core.KeyedSetupSyntax.instDecidableEqMsg") (parent := "core_keyed_setup") (tags := "milestone")
The CRS and key-generation skeleton common to every keyed scheme: the
CRS family `Crs secParam n`, the carriers `Msg`, `Sk`, and `Pp` selected
by a CRS, and the algorithms `setup` and `keygen`. `MsgVec` abbreviates
the attribute vector `Fin n → Msg crs`, the paper's `m⃗ ∈ M^n`.
`DecidableEqMsg` carries decidable equality on the message space, which
the security games need for their freshness checks.
:::

# Algebraic MAC

:::group "core_amac"
Algebraic MAC
:::

The syntax of O24 Section 3.2, Definition 3.1: an algebraic MAC
`MAC = (S, K, M, V)` for `n` attributes over a message family, with
correctness (every honestly generated MAC verifies) and UF-CMVA
(unforgeability under chosen-message and verification attacks) as the
target security notion. The abstract framework's extractability chapter
then proves the bridge from MAC UF-CMVA to KVAC extractability.

:::definition "algebraic_mac" (lean := "KVAC.Core.AlgebraicMACSyntax, KVAC.Core.Correct, KVAC.Core.AlgebraicMAC") (parent := "core_amac") (tags := "paper, O24 Def 3.1")
*O24 Definition 3.1.* Syntax of an algebraic message authentication code
for `n` attributes over a prime-order group: the algorithms `Setup`,
`KeyGen`, `MAC`, and `Verify`. The setup half is inherited from
{uses "keyed_setup"}[].
:::

:::definition "ufcmva_game" (lean := "KVAC.Core.SignedLog, KVAC.Core.UFQuery, KVAC.Core.UFOracleSpec, KVAC.Core.ufOracleImpl, KVAC.Core.UFAdversary, KVAC.Core.UF_CMVAGame, KVAC.Core.UF_CMVAAdv") (parent := "core_amac") (tags := "paper, O24 Fig 5")
*O24 Figure 5.* The unforgeability-under-chosen-message-and-verification
(UF-CMVA) security game for an algebraic MAC {uses "algebraic_mac"}[]: the
adversary holds signing and verification oracles and must forge a valid
tag on an unqueried message vector.
:::
