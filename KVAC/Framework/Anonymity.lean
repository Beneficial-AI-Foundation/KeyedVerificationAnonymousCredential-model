/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Framework.Syntax
import KVAC.Core.NIZKP.Security
import VCVio.OracleComp.ProbComp

/-!
# Anonymity game for a keyed-verification credential (O24 §4.3, Definition 4.4)

The real-versus-simulated indistinguishability game of O24 Definition 4.4. An
adversary `A` plays the issuer. It holds the secret key, a predicate `φ` and an
attribute vector `m` with `φ(m) = 1`, and it interacts with either the honest
user `KVAC.I.Usr(pp, m, φ)` or the issuance simulator `Sim.I(pp, φ)`, which does
not know `m`. A distinguisher `D` then receives `A`'s state and queries a
`Present` oracle that answers either with the honest presentation
`KVAC.P.Usr(pp, m, σ, φ')` or with the presentation simulator `Sim.P(st_Sim, φ')`.
The advantage is the distinguishing advantage between the two worlds.

## Departures from the paper's notation

- **Parameters, not sampling.** Definition 4.4 quantifies over every
  `crs ∈ [KVAC.S(1^λ, n)]`, every `(sk, pp) ∈ [KVAC.K(crs)]`, every `m` and every
  `φ` with `φ(m) = 1`. The games take these as parameters, together with the
  random-oracle cache `cache₀` left by setup and key generation, and the
  theorems that bound the advantage carry the support hypotheses, in the style
  of `newUsr_mac_isSome`. The zero-knowledge advantage `ZKAdv` samples the crs
  inside its game, so a theorem relating the two must bridge pointwise and
  sampled setup. That bridge belongs to the theorem, not to this definition.
- **One-round issuance.** `Sim.I(pp, φ)` is an interactive procedure in the
  paper. Every O24 issuance protocol is one round, so Definition 4.2 splits
  the user's side `KVAC.I.Usr` into two non-interactive algorithms with a
  state between them, and the interaction with an issuer `Srv` is their
  composition around the issuer's reply,

  ```
  Usr(pp, m, φ) <-> Srv  =  let (st, μ) <- Usr₁(pp, m, φ)
                            let σ'     <- Srv(μ)
                            Usr₂(st, σ')
  ```

  `KVACSyntax` has the halves as `issueUsr₁` and `issueUsr₂`, and `issue`
  composes them with the honest `issueSrv`. The simulator gets the same two
  moves, `simI₁` and `simI₂`, and `anonIssuance` composes either pair with the
  adversary in the issuer's place. The adversary prepares with oracle access,
  receives the first message and answers the second. The preparation phase
  keeps the adversary an arbitrary oracle algorithm, so that it can detect
  oracle programming by a simulator's first move.
- **`Option` results.** The issuer's response and the user's unblinding may
  fail, as `issueSrv` and `issueUsr₂` do. When they fail the user holds no
  credential and `Present` answers `none`. The simulator's second move may fail
  the same way, since it stands in for `KVAC.I.Usr₂`, which Definition 4.2 lets
  abort on the issuer's response.
- **One random-oracle table.** The issuer adversary, the distinguisher, the
  honest user and the simulator share one lazily sampled random oracle, threaded
  through every step. The simulator runs in `StateT HS.spec.QueryCache ProbComp`,
  so that it may read and reprogram the table, the power O24 §3.3 grants a
  simulator.
- **Negligibility over instance families.** The definition asks for one
  simulator making the advantage negligible in `λ` for all efficient `A, D` at
  every `crs`, key pair, `m` and `φ`. Since the advantage is pointwise, the
  asymptotic predicate `Anonymous` quantifies over families of instances
  indexed by the security parameter, one `AnonInstance` per `λ`, each drawn
  from the supports of setup and key generation. The statistical variant drops
  the efficiency guard, and the everlasting forward variant keeps it on the
  issuer adversary alone.
-/

namespace KVAC.Framework

open OracleComp OracleSpec KVAC.Core ENNReal

/-! ## The parties -/

/-- The anonymity simulator `Sim = (Sim.I, Sim.P)` of O24 §4.3 and Definition 4.4.

`Sim.I(pp, φ)` is the user's side of the interaction
`(st_Sim; st_A) <- (Sim.I(pp, φ) <-> A(sk, pp, φ, m))`, the simulated world's
counterpart of `(σ; st_A) <- (KVAC.I.Usr(pp, m, φ) <-> A(sk, pp, φ, m))`. The
interaction is one round, so it is two moves with the issuer's turn in between,
as Definition 4.2 splits `KVAC.I.Usr` into `Usr₁` and `Usr₂`. `simI₁` is the
move that opens the interaction and sends the request `μ`. `simI₂` is the move
that receives the issuer's response `σ'` and closes the interaction with
`st_Sim`, or rejects. `Sim.P(st_Sim, φ')` is not interactive and is `simP`.
All three run in the random-oracle state monad, so they can read and
reprogram the oracle table, the power O24 §3.3 grants a simulator. A simulator
without it would define a stronger notion than the paper's. -/
structure AnonSimulator (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS))) where
  /-- The simulator state `st_Sim`, selected by the crs. -/
  SimState : {secParam n : Nat} → kvac.Crs secParam n → Type
  /-- `Sim.I`, first move. From the public parameters and the predicate, an
  issuance request `μ` and a state, without the attribute vector. -/
  simI₁ : {secParam n : Nat} → (crs : kvac.Crs secParam n) → (pp : kvac.Pp crs) →
    (φ : kvac.Pred crs) → StateT HS.spec.QueryCache ProbComp (SimState crs × kvac.IssueMsg crs)
  /-- `Sim.I`, second move. From the state and the issuer's response, the final
  state `st_Sim`, or `none` when the simulator rejects the response. -/
  simI₂ : {secParam n : Nat} → (crs : kvac.Crs secParam n) → (st : SimState crs) →
    (σ' : kvac.BlindCred crs) → StateT HS.spec.QueryCache ProbComp (Option (SimState crs))
  /-- `Sim.P(st_Sim, φ')`, a simulated presentation. -/
  simP : {secParam n : Nat} → (crs : kvac.Crs secParam n) → (stSim : SimState crs) →
    (φ' : kvac.Pred crs) → StateT HS.spec.QueryCache ProbComp (kvac.PresentMsg crs)

end KVAC.Framework
