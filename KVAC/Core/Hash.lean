/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Hash and random-oracle interfaces (O24 §3, Notation)

Abstract interfaces for the hash functions of Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552 (§3,
Notation paragraph): `H_p : {0,1}* → ℤ_p` for Fiat–Shamir transcript hashing
and `H_𝔾 : {0,1}* → 𝔾` for hash-to-curve. Hash usage appears throughout
§4–§6; both hashes are modelled as random oracles.

Following the pattern of `Core/AlgebraicMAC`, the file provides an abstract
interface together with a concrete VCV-io binding:

- `HashSpec` — the abstract interface: a hash's domain and range, packaged
  with the instances a random-oracle implementation needs (decidable equality
  on the domain to cache queries, sampleability of the range to answer fresh
  ones).
- `HashSpec.spec` — the induced VCV-io oracle signature `Dom →ₒ Rng`, the
  single arm a computation queries to hash.
- `HashSpec.roImpl` — the concrete binding: VCV-io's lazy caching
  `randomOracle` over a `QueryCache`, answering each fresh query uniformly
  and repeated queries consistently.
- `transcriptHashSpec` / `curveHashSpec` — the paper's two instantiations
  `H_p` and `H_𝔾`.

## Design notes

**Domains stay abstract — with an encoding obligation at use sites.** The
paper's domain `{0,1}*` is the encoding of whatever data is hashed
(Fiat–Shamir transcripts, group-element derivation strings). Fixing a
bitstring type here would force every caller through an encoding layer;
instead each scheme picks its own structured domain type. This is a
*stronger* oracle model than the paper's: a random oracle on a structured
type answers distinct Lean values independently, whereas a real `{0,1}*`
oracle identifies values whose serializations collide. A concrete
instantiation therefore owes (i) an injective canonical encoding of its
domain type into bitstrings and (ii) domain-separation tags wherever two
uses share one oracle — obligations discharged at the instantiation layer,
not here.

**One oracle per hash; combine at the signature level.** `roImpl` binds a
single hash. Two independent hashes (`H_p` and `H_𝔾` in the same protocol)
cannot be combined at the implementation level — `Hp.roImpl + Hg.roImpl` is
ill-typed, the two `StateT` caches differ. Instead sum the *signatures* and
run one `randomOracle` over the sum's cache: a computation takes
`Hp.spec + Hg.spec`, and the sum's tags keep the two oracles independent.

**The structure is not indexed by a security parameter.** `H_p`'s range
`ℤ_p` depends on the group of order `p` fixed at setup, but this needs no
indexed structure: a security-parameter-indexed hash is simply a family
`ℕ → HashSpec` (or `Crs secParam → HashSpec` when tied to a crs), exactly as
an indexed carrier is a family into `Type`. Declared per use site when a
scheme needs it.

`HashSpec` originated in the zero-knowledge game of
`Core/NIZKP/Security.lean` (PR #47), which should import it from here once
both land.
-/

namespace KVAC.Core

open OracleComp OracleSpec

/-- Hash / random-oracle interface (O24 §3, Notation). Packages a hash's
domain and range with the instances VCV-io's lazy `randomOracle` needs:
decidable equality on the domain to cache queries, sampleability of the range
to answer fresh ones uniformly.

The paper's two hashes are `transcriptHashSpec` (`H_p`) and `curveHashSpec`
(`H_𝔾`). -/
structure HashSpec where
  /-- The hash domain (the paper's `{0,1}*`; in practice a structured type
  such as Fiat–Shamir transcripts). -/
  Dom : Type
  /-- The hash range (e.g. the challenge field `ℤ_p`, or the group `𝔾`). -/
  Rng : Type
  /-- Decidable equality on the domain, required to cache random-oracle
  queries. -/
  [domDecEq : DecidableEq Dom]
  /-- Sampleability of the range, required to answer fresh random-oracle
  queries uniformly. -/
  [rngSampleable : SampleableType Rng]

attribute [instance] HashSpec.domDecEq HashSpec.rngSampleable

namespace HashSpec

/-- The VCV-io oracle signature of a hash: one arm per domain element,
answering in the range. A computation with hash access takes `H.spec` (or a
sum containing it) as its `OracleSpec`.

An `abbrev` (not a `def`) so that instance resolution sees through it — e.g.
`roImpl` needs `SampleableType (H.spec.Range t)` to reduce to
`SampleableType H.Rng` and hit `rngSampleable`. -/
abbrev spec (H : HashSpec) : OracleSpec H.Dom := H.Dom →ₒ H.Rng

/-- The concrete VCV-io binding: the hash as a lazily sampled random oracle.
On a fresh query it samples the answer uniformly from `H.Rng` and caches it;
on a repeated query it answers from the cache. The cache is the `StateT`
state, so games can inspect or reprogram it.

Consistency (same query, same answer) holds for queries answered *through
this implementation*; code holding the `StateT` state can overwrite an
already-answered entry, after which the same query answers differently. A
reprogramming simulator that must stay consistent should only program fresh
(unqueried) points — a discipline enforced at the game layer, not here. -/
def roImpl (H : HashSpec) :
    QueryImpl H.spec (StateT H.spec.QueryCache ProbComp) :=
  randomOracle

/-- The paper's `H_p : {0,1}* → ℤ_p` (O24 §3, Notation): the Fiat–Shamir
transcript hash, ranging over the scalar field of the group fixed at setup.

An unconstrained convenience constructor anchoring the paper's name — it does
not (and cannot, at this layer) demand that `F` be the scalar field of
anything; a scheme instantiates it with its actual field and that choice is
checked where the hash is used. -/
def transcriptHashSpec (Dom F : Type) [DecidableEq Dom] [SampleableType F] :
    HashSpec :=
  ⟨Dom, F⟩

/-- The paper's `H_𝔾 : {0,1}* → 𝔾` (O24 §3, Notation): hash-to-curve,
ranging over the prime-order group of `Core/Group.lean`.

Like `transcriptHashSpec`, an unconstrained convenience constructor — the
prime-order structure of `G` is demanded by the scheme using the hash
(via `PrimeOrderGroup`/`SampleableGroup`), not by this definition. -/
def curveHashSpec (Dom G : Type) [DecidableEq Dom] [SampleableType G] :
    HashSpec :=
  ⟨Dom, G⟩

end HashSpec

end KVAC.Core
