/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Construction
import KVAC.Core.Hash
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append

/-!
# Zero-knowledge for a non-interactive proof system (O24 §3.3)

The two-world zero-knowledge game of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §3.3, on an
`NIZKPSyntax ProbComp`, following `AlgebraicMAC/Security.lean`.

O24 §3.3: a proof system is zero-knowledge if there is a simulator `Sim` such
that for every adversary A,

  Adv^zk = |Pr[b'=1 : crs ← S; b' ← A^Prove₀(crs)] − Pr[b'=1 : crs ← S; b' ← A^Prove₁(crs)]|

is negligible in λ, where Proveᵦ(x, w) checks (x, w) ∈ R and returns
ZKP.P(crs, x, w) when b = 0 and Sim(crs, x) when b = 1. Both A and `Sim` have
random-oracle access, and `Sim` may reprogram it.

The oracle answer type is `Option (Proof crs)`: a query outside the relation
answers `none` (the paper's implicit ⊥), identically in both worlds, so the
guard itself gives no distinguishing signal. The check needs the relation
decidable, supplied as a `DecidableRelation` argument to the games.

## The random oracle

`NIZKPSyntax` stays clean: the scheme is `ProbComp`, with no hash types among its
S/P/V fields, faithful to §3.3, where H appears only in the zero-knowledge
definition. The random oracle enters through the `HashSpec` interface (imported
from `Core/Hash.lean`): a signature `Dom →ₒ Rng` interpreted by VCV-io's
`randomOracle` over a `QueryCache`. VCV-io calls this implementation the *lazy*
random oracle
(`uniformSampleImpl.withCaching`): it samples a fresh uniform answer on first
query and caches it for consistency, in contrast to the pre-seeded
`eagerRandomOracle`. The honest computation stays `ProbComp`; the oracle lives
at the game boundary.

The simulator runs in `StateT (Dom →ₒ Rng).QueryCache ProbComp`, giving it read
and write access to the oracle cache — the reprogramming O24 grants it. The real
prover is lifted from `ProbComp` and does not touch the cache.

## Layout

- `HashSpec` — the random-oracle / hash interface, imported from `Core/Hash.lean`.
- `NIZKPSyntax.DecidableRelation` — decidability of the relation family, for
  the `(x, w) ∈ R` guard of Proveᵦ.
- `ZKQuery` / `ZKProveSpec` — the `Prove` oracle arm.
- `ZKRO` / `zkROImpl` — unifSpec + the lazy random oracle `H.spec`.
- `ZKAdversary` — an `OracleComp`-valued program with `Prove` and RO access,
  returning a guess bit.
- `zkProveReal` / `zkProveSim` — the two `QueryImpl`s answering `Prove` with the
  real prover (world 0) and the simulator (world 1), both behind the
  `(x, w) ∈ R` guard.
- `zkGameReal` / `zkGameSim` — the experiments as `ProbComp Bool`.
- `ZKAdv` — the distinguishing advantage `boolDistAdvantage` between them.

A scheme is zero-knowledge if some `Sim` makes `ZKAdv` negligible in `secParam`
for every PPT adversary. The asymptotic / negligibility statement is deferred,
because it must be proved for a concrete scheme (μCMZ, μBBS), and is not part of
defining zero-knowledge.
-/

namespace KVAC.Core

open OracleComp OracleSpec

/-- Decidability of the crs-indexed relation family. The Proveᵦ oracle of O24
§3.3 checks `(x, w) ∈ R` before answering, so the games need the check
computable. -/
abbrev NIZKPSyntax.DecidableRelation {M : Type → Type} [Monad M]
    (zkp : NIZKPSyntax M) :=
  ∀ {secParam : Nat} (crs : zkp.Crs secParam) (x : zkp.Stmt crs)
    (w : zkp.Witness crs), Decidable (zkp.relation crs x w)

/-- The `Prove` oracle arm for a fixed crs: `prove x w` requests a proof for the
witnessed instance `(x, w)`. -/
inductive ZKQuery (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : Type where
  | prove : zkp.Stmt crs → zkp.Witness crs → ZKQuery zkp crs

/-- The `OracleSpec` of the `Prove` arm: `prove x w` answers with a proof, or
`none` (the paper's implicit ⊥) when `(x, w) ∉ R`.

Formalizes the Proveᵦ oracle of O24 §3.3, the oracle A calls in `A^Proveᵦ(crs)`. -/
def ZKProveSpec (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) : OracleSpec (ZKQuery zkp crs)
  | .prove _ _ => Option (zkp.Proof crs)

/-- The random-oracle side of the interface: uniform sampling plus a lazy random
oracle with signature `H.Dom →ₒ H.Rng`.

Formalizes the random oracle of O24 §3.3 ("both adversary and simulator have
access to a random oracle"). -/
abbrev ZKRO (H : HashSpec) : OracleSpec (ℕ ⊕ H.Dom) := unifSpec + H.spec

/-- The full oracle interface a zero-knowledge adversary sees for a fixed crs:
the `Prove` arm together with `ZKRO`.

Formalizes the oracle access of `A^Proveᵦ` in O24 §3.3: the Proveᵦ oracle and the
random oracle together. -/
abbrev ZKAdvSpec (zkp : NIZKPSyntax ProbComp) {secParam : Nat}
    (crs : zkp.Crs secParam) (H : HashSpec) :
    OracleSpec (ZKQuery zkp crs ⊕ (ℕ ⊕ H.Dom)) :=
  ZKProveSpec zkp crs + ZKRO H

/-- A zero-knowledge adversary: given the crs, it queries `Prove` and the random
oracle, and outputs a guess bit `b'`. -/
structure ZKAdversary (zkp : NIZKPSyntax ProbComp) (H : HashSpec) where
  run : {secParam : Nat} → (crs : zkp.Crs secParam) →
    OracleComp (ZKAdvSpec zkp crs H) Bool

/-- A simulator `Sim(crs, x)`: produces a proof from the statement alone, running
in the random-oracle state monad so it may inspect and reprogram the cache.

Formalizes Sim of O24 §3.3; the state monad realizes "the simulator can
explicitly re-program the random oracle". -/
abbrev ZKSimulator (zkp : NIZKPSyntax ProbComp) (H : HashSpec) : Type :=
  {secParam : Nat} → (crs : zkp.Crs secParam) → zkp.Stmt crs →
    StateT (H.spec.QueryCache) ProbComp (zkp.Proof crs)

/-- Interpretation of `ZKRO`: uniform sampling by the lifted identity
implementation, the random oracle by the lazy `randomOracle`.

Operational semantics of the O24 §3.3 random oracle (lazy, consistent); machinery
realizing the oracle, not a distinct paper object. -/
def zkROImpl (H : HashSpec) :
    QueryImpl (ZKRO H) (StateT (H.spec.QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (H.spec.QueryCache) ProbComp) + H.roImpl

/-- World 0: when `(x, w) ∈ R`, answer `Prove` with the real prover
`ZKP.P(crs, x, w)`, lifted from `ProbComp` into the random-oracle state monad;
otherwise answer `none`.

Formalizes Prove₀ of O24 §3.3: Proveᵦ(x, w) checks (x, w) ∈ R and outputs
ZKP.P(crs, x, w) when b = 0. -/
def zkProveReal (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (decR : zkp.DecidableRelation) {secParam : Nat} (crs : zkp.Crs secParam) :
    QueryImpl (ZKProveSpec zkp crs) (StateT (H.spec.QueryCache) ProbComp)
  | .prove x w =>
    letI := decR crs x w
    if zkp.relation crs x w then some <$> liftM (zkp.prove crs x w) else pure none

/-- World 1: when `(x, w) ∈ R`, answer `Prove` with the simulator `Sim(crs, x)`,
ignoring the witness; otherwise answer `none`. The guard reads the witness, so
the two worlds reject exactly the same queries.

Formalizes Prove₁ of O24 §3.3: Proveᵦ(x, w) checks (x, w) ∈ R and outputs
Sim(crs, x) when b = 1. -/
def zkProveSim (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (decR : zkp.DecidableRelation) (sim : ZKSimulator zkp H) {secParam : Nat}
    (crs : zkp.Crs secParam) :
    QueryImpl (ZKProveSpec zkp crs) (StateT (H.spec.QueryCache) ProbComp)
  | .prove x w =>
    letI := decR crs x w
    if zkp.relation crs x w then some <$> sim crs x else pure none

/-- Run adversary `A` against a given `Prove` implementation with a fresh (empty)
random-oracle cache, returning its guess bit as a `ProbComp Bool`.

Formalizes the experiment body of O24 §3.3: crs ← ZKP.S(1^λ); b' ← A^Proveᵦ(crs). -/
def zkRun (zkp : NIZKPSyntax ProbComp) (H : HashSpec) (A : ZKAdversary zkp H)
    (proveImpl : {secParam : Nat} → (crs : zkp.Crs secParam) →
      QueryImpl (ZKProveSpec zkp crs) (StateT (H.spec.QueryCache) ProbComp))
    (secParam : Nat) : ProbComp Bool := do
  let crs ← zkp.setup secParam
  (simulateQ (proveImpl crs + zkROImpl H) (A.run crs)).run' ∅

/-- The real-world experiment (b = 0).

Formalizes the b = 0 world of O24 §3.3: crs ← S; b' ← A^Prove₀(crs). -/
def zkGameReal (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (decR : zkp.DecidableRelation) (A : ZKAdversary zkp H)
    (secParam : Nat) : ProbComp Bool :=
  zkRun zkp H A (fun crs => zkProveReal zkp H decR crs) secParam

/-- The simulated-world experiment (b = 1).

Formalizes the b = 1 world of O24 §3.3: crs ← S; b' ← A^Prove₁(crs). -/
def zkGameSim (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (decR : zkp.DecidableRelation) (A : ZKAdversary zkp H)
    (sim : ZKSimulator zkp H) (secParam : Nat) : ProbComp Bool :=
  zkRun zkp H A (fun crs => zkProveSim zkp H decR sim crs) secParam

/-- The zero-knowledge advantage of `A` with respect to simulator `sim`: the
distinguishing advantage between the real and simulated worlds. Zero-knowledge
holds if some `sim` makes this negligible in `secParam` for every PPT `A`; the
asymptotic statement is deferred.

Formalizes Adv^zk_{ZKP,A}(λ) of O24 §3.3, the difference of the two worlds'
probabilities |Pr[b'=1 | b=0] − Pr[b'=1 | b=1]|.

An `abbrev`, like `UF_CMVAAdv` and `qdlAdv`, so it unfolds in downstream
reduction proofs. -/
noncomputable abbrev ZKAdv (zkp : NIZKPSyntax ProbComp) (H : HashSpec)
    (decR : zkp.DecidableRelation) (A : ZKAdversary zkp H)
    (sim : ZKSimulator zkp H) (secParam : Nat) : ℝ :=
  ProbComp.boolDistAdvantage (zkGameReal zkp H decR A secParam)
    (zkGameSim zkp H decR A sim secParam)

end KVAC.Core
