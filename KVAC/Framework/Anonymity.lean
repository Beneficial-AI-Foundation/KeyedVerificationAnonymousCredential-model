/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Framework.Syntax
import KVAC.Framework.Extractability
import KVAC.Core.NIZKP.Security
import VCVio.OracleComp.ProbComp
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.Asymptotics.Negligible

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

/-! ## The `Present` oracle, what the distinguisher sees -/

/-- The single oracle call of Definition 4.4, `Present_b(φ')`, for a fixed crs. -/
inductive AnonQuery {M : Type → Type} [Monad M] (kvac : KVACSyntax M)
    {secParam n : Nat} (crs : kvac.Crs secParam n) : Type where
  /-- `Present_b(φ')`, a presentation request under the predicate `φ'`. -/
  | present : kvac.Pred crs → AnonQuery kvac crs

/-- Answer type of `Present_b(φ')`. A presentation message, or `none` when
`φ'(m) = 0` or when the user holds no credential because issuance failed. -/
def AnonPresentSpec {M : Type → Type} [Monad M] (kvac : KVACSyntax M)
    {secParam n : Nat} (crs : kvac.Crs secParam n) : OracleSpec (AnonQuery kvac crs)
  | .present _ => Option (kvac.PresentMsg crs)

/-- The oracle interface the distinguisher `D` sees for a fixed crs, the
`Present_b` oracle together with the random oracle. -/
abbrev AnonDistSpec (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    {secParam n : Nat} (crs : kvac.Crs secParam n) :
    OracleSpec (AnonQuery kvac crs ⊕ (ℕ ⊕ HS.Dom)) :=
  AnonPresentSpec kvac crs + ZKRO HS

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

/-- The issuer adversary `A(sk, pp, φ, m)` of Definition 4.4, the right side of
the interactions `(σ; st_A) <- (KVAC.I.Usr(pp, m, φ) <-> A(sk, pp, φ, m))` and
`(st_Sim; st_A) <- (Sim.I(pp, φ) <-> A(sk, pp, φ, m))`.

The interaction is one round. The user side speaks first with the request `μ`,
`A` answers with the issuer's response `σ'`, and the user side closes. `A`'s
part of it is therefore two runs around one message. `prepare` is everything
`A` does before `μ` arrives, with random oracle access, since an oracle
algorithm queries at any time and a simulator that programs the oracle at its
first move is detectable only by an adversary that queried earlier. `respond`
is `A` on `μ`, returning `σ'`, or `none` to reject as `issueSrv` may, and the
state `st_A` the interaction outputs on `A`'s side. `Pre` carries `A` across
the user's move, and `StA` is the type of `st_A`, which the distinguisher
receives. -/
structure AnonIssuer (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS))) where
  /-- The private state `A` keeps from its preparation to its response,
  selected by the crs. -/
  Pre : {secParam n : Nat} → kvac.Crs secParam n → Type
  /-- The state `st_A` passed to the distinguisher, selected by the crs. -/
  StA : {secParam n : Nat} → kvac.Crs secParam n → Type
  /-- `A(sk, pp, φ, m)` before the user's request, with random oracle access. -/
  prepare : {secParam n : Nat} → (crs : kvac.Crs secParam n) → (sk : kvac.Sk crs) →
    (pp : kvac.Pp crs) → (φ : kvac.Pred crs) → (m : kvac.MsgVec crs) →
    OracleComp (ZKRO HS) (Pre crs)
  /-- `A` on the user's request `μ`, from its private state. -/
  respond : {secParam n : Nat} → (crs : kvac.Crs secParam n) → (pre : Pre crs) →
    (μ : kvac.IssueMsg crs) → OracleComp (ZKRO HS) (Option (kvac.BlindCred crs) × StA crs)

/-- The distinguisher `D^{Present_b}(st_A)` of Definition 4.4. It takes no part
in the interaction. It receives the state `st_A` the interaction output on
`A`'s side, queries the `Present_b` oracle and the random oracle, and outputs
the guess `b'`. The state type `StA` is a parameter, so that `A` and `D` stay
two adversaries with two efficiency notions, as the statistical and
everlasting variants of the definition require. -/
structure AnonDistinguisher (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (StA : {secParam n : Nat} → kvac.Crs secParam n → Type) where
  /-- `D^{Present_b}(st_A)`. -/
  run : {secParam n : Nat} → (crs : kvac.Crs secParam n) → (stA : StA crs) →
    OracleComp (AnonDistSpec HS kvac crs) Bool

/-! ## The game, how the oracle answers and the two worlds -/

/-- The monad the `Present` oracle runs in. The shared random-oracle cache and
the user's or simulator's state `S`, `none` when issuance failed, in one
`StateT` over `ProbComp`. -/
abbrev AnonComp (HS : HashSpec) (S : Type) : Type → Type :=
  StateT (HS.spec.QueryCache × Option S) ProbComp

/-- `Present_b(φ')` of Definition 4.4, generic in the world. The oracle "checks if
`φ'(m)` holds for `m`, and if so returns" the presentation `pres s φ'` computed
from the stored state `s`. World `b = 0` supplies the honest `KVAC.P.Usr` on the
credential, world `b = 1` supplies `Sim.P` on the simulator state. A failed
issuance (`none` state) answers `none`. -/
def anonPresentImpl (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    {secParam n : Nat} (crs : kvac.Crs secParam n) (m : kvac.MsgVec crs) {S : Type}
    (pres : S → kvac.Pred crs → StateT HS.spec.QueryCache ProbComp (kvac.PresentMsg crs)) :
    QueryImpl (AnonPresentSpec kvac crs) (AnonComp HS S)
  | .present φ' => StateT.mk fun (cache, st?) => do
      match st? with
      | none => pure (none, (cache, none))
      | some s =>
        if kvac.holds crs φ' m then
          let (ρ, cache') ← (pres s φ').run cache
          pure (some ρ, (cache', some s))
        else pure (none, (cache, some s))

/-- The random-oracle handler over the `Present` oracle's state. The
distinguisher's direct `ZKRO HS` queries hit the same table the presentations
use, as `extROImpl` arranges for the extraction game. -/
def anonROImpl (HS : HashSpec) (S : Type) : QueryImpl (ZKRO HS) (AnonComp HS S) :=
  fun q => StateT.mk fun (cache, st) => do
    let (a, cache') ← (zkROImpl HS q).run cache
    pure (a, (cache', st))

/-- The issuance phase shared by both worlds. The adversary prepares first. The
user side is abstract, a first move producing a request from `pp` and `φ`, and
a second move producing the stored state `S` from the issuer's response. World
`b = 0` instantiates it with `issueUsr₁` and `issueUsr₂`, world `b = 1` with
`Sim.I`'s two moves. Returns the adversary state `st_A`, the stored state
(`none` on rejection or abort), and the random-oracle cache after the phase. -/
def anonIssuance (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (issuer : AnonIssuer HS kvac) {secParam n : Nat} (crs : kvac.Crs secParam n)
    (sk : kvac.Sk crs) (pp : kvac.Pp crs) (m : kvac.MsgVec crs) (φ : kvac.Pred crs)
    {U S : Type}
    (usr₁ : StateT HS.spec.QueryCache ProbComp (U × kvac.IssueMsg crs))
    (usr₂ : U → kvac.BlindCred crs → StateT HS.spec.QueryCache ProbComp (Option S))
    (cache₀ : HS.spec.QueryCache) :
    ProbComp (issuer.StA crs × Option S × HS.spec.QueryCache) := do
  -- A(sk, pp, φ, $\vec{m}$) prepares, with random oracle access, before the user speaks.
  let (pre, cache₁) ← runRO HS cache₀ (issuer.prepare crs sk pp φ m)
  -- The user's (or simulator's) request.
  let ((stU, μ), cache₂) ← usr₁.run cache₁
  -- (σ'; st_A) ← A on μ.
  let ((σ'?, stA), cache₃) ← runRO HS cache₂ (issuer.respond crs pre μ)
  -- The user's (or simulator's) check and unblinding.
  match σ'? with
  | none    => pure (stA, none, cache₃)
  | some σ' =>
    let (s?, cache₄) ← (usr₂ stU σ').run cache₃
    pure (stA, s?, cache₄)

/-- World `b = 0` of Definition 4.4. Honest issuance
`(σ; st_A) ← (KVAC.I.Usr(pp, m, φ) <-> A(sk, pp, φ, m))`, then
`b' ← D^{Present₀}(st_A)` with `Present₀(φ') = KVAC.P.Usr(pp, m, σ, φ')`. -/
def anonGameReal (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (issuer : AnonIssuer HS kvac) (distinguisher : AnonDistinguisher HS kvac issuer.StA)
    {secParam n : Nat} (crs : kvac.Crs secParam n) (sk : kvac.Sk crs) (pp : kvac.Pp crs)
    (m : kvac.MsgVec crs) (φ : kvac.Pred crs) (cache₀ : HS.spec.QueryCache) :
    ProbComp Bool := do
  let (stA, σ?, cache) ← anonIssuance HS kvac issuer crs sk pp m φ
    (simulateQ (zkROImpl HS) (kvac.issueUsr₁ crs pp m φ))
    (fun stU σ' => simulateQ (zkROImpl HS) (kvac.issueUsr₂ crs stU σ')) cache₀
  let oracles :=
    anonPresentImpl HS kvac crs m
      (fun σ φ' => simulateQ (zkROImpl HS) (kvac.presentUsr crs pp m σ φ')) +
    anonROImpl HS (kvac.Cred crs)
  (simulateQ oracles (distinguisher.run crs stA)).run' (cache, σ?)

/-- World `b = 1` of Definition 4.4. Simulated issuance
`(st_Sim; st_A) ← (Sim.I(pp, φ) <-> A(sk, pp, φ, m))`, then
`b' ← D^{Present₁}(st_A)` with `Present₁(φ') = Sim.P(st_Sim, φ')`. The
simulator never receives the attribute vector `m`. Only `A` receives it, as
the definition gives it to `A`, and the `Present` oracle reads it for the check
`φ'(m) = 1`. -/
def anonGameSim (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (issuer : AnonIssuer HS kvac) (distinguisher : AnonDistinguisher HS kvac issuer.StA)
    (sim : AnonSimulator HS kvac) {secParam n : Nat} (crs : kvac.Crs secParam n)
    (sk : kvac.Sk crs) (pp : kvac.Pp crs) (m : kvac.MsgVec crs) (φ : kvac.Pred crs)
    (cache₀ : HS.spec.QueryCache) : ProbComp Bool := do
  let (stA, st?, cache) ← anonIssuance HS kvac issuer crs sk pp m φ
    (sim.simI₁ crs pp φ) (sim.simI₂ crs) cache₀
  let oracles :=
    anonPresentImpl HS kvac crs m (sim.simP crs) + anonROImpl HS (sim.SimState crs)
  (simulateQ oracles (distinguisher.run crs stA)).run' (cache, st?)

/-- The anonymity advantage `Adv^anon_{KVAC,A,D}` of Definition 4.4 at fixed
`crs`, keys, attribute vector, predicate and initial cache, with respect to the
simulator `sim`. The distinguishing advantage between the two worlds,
`|Pr[b' = 1 | b = 0] − Pr[b' = 1 | b = 1]|`. `Anonymous` below asks some `sim`
to make it negligible for every efficient `(A, D)`, and `StatisticallyAnonymous`
for every `(A, D)`. An `abbrev`, so it unfolds in the proofs of those
predicates for concrete schemes. -/
noncomputable abbrev AnonAdv (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (issuer : AnonIssuer HS kvac) (distinguisher : AnonDistinguisher HS kvac issuer.StA)
    (sim : AnonSimulator HS kvac) {secParam n : Nat} (crs : kvac.Crs secParam n)
    (sk : kvac.Sk crs) (pp : kvac.Pp crs) (m : kvac.MsgVec crs) (φ : kvac.Pred crs)
    (cache₀ : HS.spec.QueryCache) : ℝ :=
  ProbComp.boolDistAdvantage (anonGameReal HS kvac issuer distinguisher crs sk pp m φ cache₀)
    (anonGameSim HS kvac issuer distinguisher sim crs sk pp m φ cache₀)

/-! ## Anonymity (O24 Definition 4.4) -/

/-- One instance of the quantifier prefix of Definition 4.4 at a fixed security
parameter and attribute count. "For all `crs ∈ [KVAC.S(1^λ, n)]` and
`(sk, pp) ∈ [KVAC.K(crs)]`, `m ∈ M^n_crs`, `φ ∈ Φ` such that `φ(m) = 1`." The
random-oracle caches left by setup and key generation come with the supports,
so the games start from the table those algorithms built.

The structure exists because `AnonAdv` is pointwise while the definition asks
for negligibility in `λ`. `Anonymous` quantifies over families of instances,
one admissible choice at each `λ`, and asks the resulting function of `λ` to be
negligible. The games and the theorems that bound `AnonAdv` take the same data
as loose arguments with support hypotheses, in the style of `newUsr_mac_isSome`,
and do not use this structure. -/
structure AnonInstance (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (secParam n : Nat) where
  /-- The common reference string `crs`. -/
  crs : kvac.Crs secParam n
  /-- The random-oracle table setup leaves. -/
  cacheSetup : HS.spec.QueryCache
  /-- `crs ∈ [KVAC.S(1^λ, n)]`, setup run through the random oracle from the
  empty table. -/
  crs_mem : (crs, cacheSetup) ∈ support (runRO HS ∅ (kvac.setup secParam n))
  /-- The secret key `sk`. -/
  sk : kvac.Sk crs
  /-- The public parameters `pp`. -/
  pp : kvac.Pp crs
  /-- The random-oracle table key generation leaves, where the games start. -/
  cache : HS.spec.QueryCache
  /-- `(sk, pp) ∈ [KVAC.K(crs)]`, key generation run from setup's table. -/
  keys_mem : ((sk, pp), cache) ∈ support (runRO HS cacheSetup (kvac.keygen crs))
  /-- The attribute vector `m ∈ M^n_crs`. -/
  m : kvac.MsgVec crs
  /-- The predicate `φ ∈ Φ`. -/
  φ : kvac.Pred crs
  /-- `φ(m) = 1`. -/
  holds_φ : kvac.holds crs φ m = true

/-- The advantage at an instance, as a nonnegative extended real for
`negligible`. -/
noncomputable def AnonInstance.adv {HS : HashSpec} {kvac : KVACSyntax (OracleComp (ZKRO HS))}
    {secParam n : Nat} (inst : AnonInstance HS kvac secParam n)
    (issuer : AnonIssuer HS kvac) (distinguisher : AnonDistinguisher HS kvac issuer.StA)
    (sim : AnonSimulator HS kvac) : ℝ≥0∞ :=
  ENNReal.ofReal
    (AnonAdv HS kvac issuer distinguisher sim inst.crs inst.sk inst.pp inst.m inst.φ inst.cache)

/-- "A non-empty message family `M`", the standing assumption of Definition 4.4.
Every crs selects a non-empty attribute type. Without it the quantification over
instance families below is vacuous at a security parameter with no attributes,
and a scheme that reveals its attributes would count as anonymous. -/
def NonemptyMsg {M : Type → Type} [Monad M] (kvac : KVACSyntax M) : Prop :=
  ∀ {secParam n : Nat} (crs : kvac.Crs secParam n), Nonempty (kvac.Msg crs)

/-- Anonymity, O24 Definition 4.4, at a fixed attribute count `n`. The message
family is non-empty, and there is a simulator `Sim = (Sim.I, Sim.P)` such that
for all adversaries `A, D` the efficiency predicate admits and every family of
instances, one per security parameter, the advantage is negligible in the
security parameter.

The order of quantifiers is the paper's, `∃ Sim` before `∀ A, D` and before the
instances. Instances come as a family indexed by `λ` because the definition
fixes `crs`, keys, `m` and `φ` pointwise while asking for negligibility in `λ`,
so the function whose decay is asked for picks one instance at each `λ`.

The efficiency predicate `isPPT` is an abstract parameter on the two
adversaries, as in `Extractable`, since the development fixes no concrete
efficiency notion on `OracleComp` adversaries. Taking it on the pair lets the
variants below constrain the issuer adversary and the distinguisher separately.
The hash specification `HS` is fixed across the security parameter, as in
`Extractable` and `ZKAdv`, the fixed-parameter modelling of issue #148. -/
def Anonymous (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (isPPT : (issuer : AnonIssuer HS kvac) → AnonDistinguisher HS kvac issuer.StA → Prop)
    (n : Nat) : Prop :=
  NonemptyMsg kvac ∧
  ∃ sim : AnonSimulator HS kvac,
    ∀ (issuer : AnonIssuer HS kvac) (distinguisher : AnonDistinguisher HS kvac issuer.StA),
      isPPT issuer distinguisher →
      ∀ inst : (secParam : Nat) → AnonInstance HS kvac secParam n,
        negligible fun secParam => (inst secParam).adv issuer distinguisher sim

/-- Anonymity with O24's side condition `n ≤ poly(λ)` made a proof obligation, as
`ExtractablePoly` does for Definition 4.5. The attribute count `n(λ)` is a function
of the security parameter, and for every polynomially bounded `n` there is a
simulator making the advantage negligible for the efficient adversaries, at
attribute count `n secParam` for each `secParam`. `Anonymous` is the fixed-`n`
slice. -/
def AnonymousPoly (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (isPPT : (issuer : AnonIssuer HS kvac) → AnonDistinguisher HS kvac issuer.StA → Prop) : Prop :=
  NonemptyMsg kvac ∧
  ∀ n : ℕ → ℕ, PolyBounded n →
    ∃ sim : AnonSimulator HS kvac,
      ∀ (issuer : AnonIssuer HS kvac) (distinguisher : AnonDistinguisher HS kvac issuer.StA),
      isPPT issuer distinguisher →
        ∀ inst : (secParam : Nat) → AnonInstance HS kvac secParam (n secParam),
          negligible fun secParam => (inst secParam).adv issuer distinguisher sim

/-- Statistical anonymity, O24 Definition 4.4. The advantage is negligible "for
unbounded adversaries `A, D`", so the efficiency guard is dropped. -/
def StatisticallyAnonymous (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (n : Nat) : Prop :=
  Anonymous HS kvac (fun _ _ => True) n

/-- Everlasting forward anonymity, O24 Definition 4.4. The advantage is
"negligible when `D` is unbounded", so the efficiency guard falls on the issuer
adversary `A` alone and the distinguisher is arbitrary. -/
def EverlastingForwardAnonymous (HS : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO HS)))
    (isPPTIssuer : AnonIssuer HS kvac → Prop) (n : Nat) : Prop :=
  Anonymous HS kvac (fun issuer _ => isPPTIssuer issuer) n

end KVAC.Framework
