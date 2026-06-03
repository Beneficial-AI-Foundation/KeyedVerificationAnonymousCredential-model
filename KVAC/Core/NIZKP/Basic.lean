/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import ToMathlib.PFunctor.Free

/-!
# A refinement approach for NIZKP specification

**Non-Interactive Zero-Knowledge Proof** (NIZKP) is a protocol where one party, the prover,
sends one message that must convince the other party, the verifier, of a statement
without revealing anything beyond its truth.

This refinement approach aims at defining a `NIZKP` that is _agnostic with respect to the
security model_.
This means that one may "plug" different security models into the abstract `NIZKP` and then
prove different security properties about the protocol.

The `NIZKPScheme` structure (`setup`/`prove`/`verify`/`relation`), together with the
properties `KnowledgeSound`, `SimulationExtractable`, and `ZeroKnowledge`, makes up the
abstract spec, parametric in an output carrier `F`. We keep `F` abstract rather than fixing it per
security model, so the abstract notions are defined once and specialize to each model
with no reproof.

We refine over `F` in three different layers, as follows:

  0. `F` is an arbitrary type constructor.
  1. `F` is `Freer G`, a free monad in the "freer" encoding. This decision
     follows the "Program is data." paradigm.
  2. `F` is `PFunctor.FreeM P`, a polynomial functor. It solves the so-called
     "universe bump" that arises in Layer 1.

## Consistency of the specification with respect to the paper

- What is consistent. The `NIZKPScheme` fields (`setup`, `prove`, `verify`, `relation`)
match the three algorithms and the relation family of O24 §3.3. The three properties
`KnowledgeSound`, `ZeroKnowledge`, and `SimulationExtractable` follow the same section
(and, for simulation-extractability, the definition O24 points to: Dao–Grubbs, ePrint
2023/494).

- Where the spec differs. The paper works only in the computational model. Here we want a
spec that also fits other models (for example the symbolic one), so we cannot put that
computational machinery into the definitions. This implies differences that are summarized below.

  * The extractor, in `KnowledgeSound` and `SimulationExtractable`. The paper obtains the
    witness from a game against a random attacker (using the attacker's code and coins);
    here `extract` is an ordinary function of `(crs, x, π)`. The attacker is gone.
  * The relation `Indist`, in `ZeroKnowledge`. The paper bounds, by a negligible amount,
    the chance of telling the prover's output from the simulator's over many queries; here
    `Indist` compares a single pair of outputs. The advantage measure is gone.
  * The relation `produces`, in `SimulationExtractable`. The paper keeps a running record
    of the proofs the simulator handed out and excludes that exact set; here `produces`
    marks the proofs the simulator could make on a statement. The query record is gone.
  * Completeness (every honest proof verifies, O24 §3.3) is left to the security model to
    define, because it is the one property that follows a single proof all the way from the
    prover that creates it to the verifier that checks it. What that proof actually is
    depends on the model, so whether the verifier accepts it depends on the model too.
    This is why there is no `Complete` definition at the abstract layer.
  * In Orrù's paper, `F` is left implicit as the paper tackles the computational model only.
    Here, we aim at a specification that is agnostic with respect to the security model.
    In the symbolic model `F Proof` is a _term_ over proofs. In the computational model, `F Proof`
    is a _distribution_ over proofs.

Reference: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint [2024/1552](https://eprint.iacr.org/2024/1552). -/

namespace KVAC.Core.NIZKP

/-! ## Layer 0 — abstract NIZKP over an arbitrary carrier `F` -/

section Layer0

universe u v
variable {F : Type u → Type v} {Crs Stmt Witness Proof : Type u}

structure NIZKPScheme (F : Type u → Type v) (Crs Stmt Witness Proof : Type u) where
  /-- `S(1^λ)`: setup on the security parameter `λ`; outputs a CRS and implicitly
  selects a relation `R ∈ R`. (O24 §3.3, algorithm `ZKP.S`.) -/
  setup : («λ» : Nat) → F Crs
  /-- `P(crs, x, w)`: prover; from a witnessed instance `(x, w) ∈ R` produces a
  proof. (O24 §3.3, algorithm `ZKP.P`.) -/
  prove : Crs → Stmt → Witness → F Proof
  /-- `V(crs, x, π)`: verifier; `true`/`false` = accept/reject. (O24 §3.3,
  algorithm `ZKP.V`, there `1`/`0`.) -/
  verify : Crs → Stmt → Proof → Bool
  /-- `relation crs x w`: `w` witnesses `x` under the relation `crs` selects
  (O24 §3.3 — a system parameter, not an algorithm). The leading `Crs →` is O24's
  crs-indexing ("setup implicitly selects `R ∈ R`"); the `λ`-family `{Rλ}` is not
  here, as `λ` enters only via `setup`. It is a field, not a parameter, so the
  security properties take it directly from the scheme (as `relation crs`) rather
  than receiving it as a separate argument. -/
  relation : Crs → Stmt → Witness → Prop

/-- A security model for the carrier `F`: the model-dependent relations the security
properties are stated against. An instance selects the model (symbolic, computational,
…) and supplies both relations consistently. -/
class SecurityModel (F : Type u → Type v) where
  /-- Indistinguishability of two `F`-computations (used by `ZeroKnowledge`). -/
  Indist : ∀ {α : Type u}, F α → F α → Prop
  /-- `produces c a` holds when `a` is a possible output of the computation `c`.
  `SimulationExtractable` uses it to single out the proofs the simulator made.
  Symbolically `c = a`; computationally `a` lies in the support of `c`. -/
  produces : ∀ {α : Type u}, F α → α → Prop

/-- Knowledge soundness: a proof can only pass verification if whoever produced it
actually knew a valid witness. We capture "knew" by exhibiting a single extractor
that pulls such a witness out of any accepting proof. -/
def KnowledgeSound (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∃ extract : Crs → Stmt → Proof → Witness,
    ∀ crs x π, nizkp.verify crs x π = true → nizkp.relation crs x (extract crs x π)

/-- Simulation-extractability: knowledge soundness that still holds when fake proofs
are around. An extractor pulls a witness out of any accepting proof except the ones
the simulator itself produced. `produces` comes from the `SecurityModel`; intended
as "`π` is a possible output of `c`" (symbolically `c = π`; computationally `π` in
the support of `c`). -/
def SimulationExtractable [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∃ sim : Crs → Stmt → F Proof,
  ∃ extract : Crs → Stmt → Proof → Witness,
    ∀ crs x π, nizkp.verify crs x π = true → ¬ SecurityModel.produces (sim crs x) π →
      nizkp.relation crs x (extract crs x π)

/-- Zero-knowledge: there is a simulator that, knowing only the statement (not the
witness), produces something `Indist` from the real prover's output. `Indist` comes
from the `SecurityModel`:
- symbolic model: `Indist := Eq` — the simulated term must be the *same term* as the
  real proof (perfect zero-knowledge, no probabilities);
- computational model: `Indist :=` "indistinguishable" — no efficient adversary tells
  the prover's and simulator's output distributions apart (negligible advantage). -/
def ZeroKnowledge [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∃ sim : Crs → Stmt → F Proof,
    ∀ crs x w, nizkp.relation crs x w →
      SecurityModel.Indist (nizkp.prove crs x w) (sim crs x)

end Layer0

/-! ## Layer 1 — first refinement: the free monad

A free monad over a set of _operations_ is the monad whose values are *programs* built
from those operations carrying no meaning until a _handler_ gives them one.
It gives us exactly the structure we want to associate different (security) models
to the set of (protocol) operations.

More technically, why move from an arbitrary `F` to a free monad? With no structure we cannot write
`prove` and `setup` as effectful programs and we cannot interpret them.
A free monad over an effect signature gives both. Being a monad, `prove` and `setup`
can be written as ordinary sequenced programs. Being *free*, it only records the operations
and computes nothing, so a program is itself a value (a tree of operations and continuations)
and carries no meaning until a handler gives it one. That is why one program can be interpreted
in more than one way: a handler turns the same `prove` into a symbolic term in one model or a
probabilistic computation in another. This is what lets `Indist` and `produces` be
derived rather than assumed. The effect signature also names exactly which effects `prove`
may use, such as sampling and oracle queries.

This layer is for explanation only. It motivates the choice of free monads for the `F`
parameter of `NIZKPScheme`. -/

section Layer1

universe u
variable {F : Type u → Type u}

-- The textbook free monad cannot be written as an inductive type in Lean. Its
-- constructor is
--   roll : F (Free F α) → Free F α
-- so `Free F α` occurs as an *argument* to `F`.
-- Lean only accepts an inductive type when every recursive occurrence is strictly _positive_,
-- that is, they only appear in the codomain.
-- This rule keeps the type well-founded and its recursor sound.
-- Here `F` is an arbitrary `Type u → Type u`, so Lean cannot check if `F` uses its
-- argument positively. For example `F` could be `fun X => X → Bool`, where `X` is the
-- placeholder standing for what type `F` is applied to. In the `roll` constructor that
-- type is `Free F α`, so `F (Free F α)` becomes `Free F α → Bool`. There, `Free F α` is a
-- _negative_ position, and the kernel rejects it.

-- The declaration below triggers exactly that rejection (its expected error is asserted):
-- error: (kernel) arg #3 of 'KVAC.Core.NIZKP.Free.roll' contains a non valid
-- occurrence of the datatypes being declared
-- (Note: rewrite the two lines above as a single line within /-- -/ and uncomment
--  the following lines to see the errors.)
-- #guard_msgs in
-- inductive Free (F : Type u → Type u) (α : Type u) : Type u where
-- | pure (a : α) : Free F α
-- | roll (x : F (Free F α)) : Free F α

/-- The freer encoding gets around that problem. A program is one of two things:
- `pure a` — finished, with result `a`; or
- `bind op k` — "run the operation `op : F ι`, then keep going with `k`", where the
  rest of the program `k : ι → Freer F α` is waiting for the operation's result of
  type `ι`.

The trick is that the recursive `Freer F α` now shows up only as the *result* of the
continuation `k`, never as an argument to `F`. -/
private inductive Freer (F : Type u → Type u) (α : Type u) : Type (u + 1) where
  | pure (a : α) : Freer F α
  | bind {ι : Type u} (op : F ι) (k : ι → Freer F α) : Freer F α

/-- "Program is data" is now usable: a handler interprets the syntax. -/
private def Freer.bindM : Freer F α → (α → Freer F β) → Freer F β
  | Freer.pure a,    g => g a
  | Freer.bind op k, g => Freer.bind op (fun x => Freer.bindM (k x) g)

private instance : Monad (Freer F) where
  pure := Freer.pure
  bind := Freer.bindM

/-- The Layer-0 notions apply verbatim at the freer carrier — no restatement. -/
example {F : Type → Type} {Crs Stmt Witness Proof : Type}
    (nizkp : NIZKPScheme (Freer F) Crs Stmt Witness Proof) : Prop :=
  KnowledgeSound nizkp

-- However, remembering each operation's result type `ι` pushes the whole type up one universe.
-- This is the so-called "universe bump" problem.
-- The universe bump, made visible: `Freer.{u} : (Type u → Type u) → Type u → Type (u+1)`.
-- The codomain is `u+1`, not `u`.
set_option pp.universes true in
#check @Freer

-- The consequence of "universe bump" problem is *non-composability*.
-- `Freer` needs its base functor to be an endofunctor `Type u → Type u`. So a freer
-- monad cannot be composed with a freer monad: freer monads do not compose
-- under the bump.
#check_failure (Freer (Freer (fun _ : Type => Unit)))

end Layer1

/-! ## Layer 2 — last refinement: the polynomial functor

The universe bump in Layer 1 came from `Freer` `bind` constructor
quantifying over an *arbitrary* result type `ι : Type u`, the type the operation returns.
A constructor that takes a `Type u` as an argument must itself live one universe above it,
which pushes the whole structure up to `Type (u+1)`.

A polynomial functor describes the operations without ever quantifying over a type. It
is a pair: `A : Type`, the set of operation names, and `B : A → Type`,
which gives each operation its result type. The operations and their result types are
fixed.

A `FreeM P` constructor takes only an operation name `a : A` together with a continuation
indexed by `B a`. The result type is obtained by applying the fixed family `B`, never taken
as a fresh type argument — unlike `Freer`, where each operation introduced its own `ι`.
Since no constructor quantifies over a type, nothing forces a level increase: `FreeM P` stays in
`Type 0`. Therefore free monads built this way compose. -/

section Layer2

/-- A polynomial functor whose operation names and result types are all small (`Type 0`),
so `PFunctor.FreeM P : Type → Type` with no universe bump. -/
abbrev SmallPFunctor := PFunctor.{0, 0}

variable {P : SmallPFunctor}

/-- A NIZKP scheme over the free monad on the effect signature `P`. This is the form
the concrete schemes (μCMZ, μBBS) are built against: `P` names the operations a proof
may use (sampling, oracle queries), composed with `+`. Being an `abbrev`, every Layer-0
property (`KnowledgeSound`, `ZeroKnowledge`, `SimulationExtractable`) applies to it
unchanged. -/
abbrev FreeNIZKPScheme (P : SmallPFunctor) (Crs Stmt Witness Proof : Type) :=
  NIZKPScheme (PFunctor.FreeM P) Crs Stmt Witness Proof

-- ### Examples for Layer 2

/-- A handler `s` (interpret the syntax into a target monad `m` via `FreeM.mapM`)
*induces* a `SecurityModel`: both model relations are refined to handler-based ones —
interpret, then compare — rather than rewritten. This is the equality-after-interpretation
family of models (symbolic, perfect); it does NOT cover the computational model, whose
`Indist` is a negligible-advantage relation rather than equality. Private: it only serves
the example below; downstream models populate `SecurityModel` directly. -/
private def handlerModel {m : Type → Type} [Monad m] (s : (a : P.A) → m (P.B a)) :
    SecurityModel (PFunctor.FreeM P) where
  Indist a b := a.mapM s = b.mapM s
  produces c a := c.mapM s = pure a

/-- `FreeM P : Type v → Type (max uA uB v)`; at `P.{0,0}, v = 0` that is
`Type 0`. So it genuinely IS a `Type → Type` endofunctor — no bump. -/
example (P : SmallPFunctor) : Type → Type := PFunctor.FreeM P

/-- The Layer-0 notions apply verbatim at the free-monad carrier — no restatement. -/
example {Crs Stmt Witness Proof : Type}
    (nizkp : FreeNIZKPScheme P Crs Stmt Witness Proof) : Prop :=
  KnowledgeSound nizkp

/-- Under the induced model, the Layer-0 `ZeroKnowledge` applies unchanged. -/
example {Crs Stmt Witness Proof : Type} {m : Type → Type} [Monad m]
    (s : (a : P.A) → m (P.B a))
    (nizkp : FreeNIZKPScheme P Crs Stmt Witness Proof) : Prop :=
  letI := handlerModel s
  ZeroKnowledge nizkp

/-- This single example witnesses the two things that make Layer 2 the usable layer.

1. Effect signatures compose by the sum `+` (VCV-io's `PFunctor.sum`): the operation
   names become `P.A ⊕ Q.A` and each keeps its own result type. Both signatures lift into
   one free monad `FreeM (P + Q)`, which still lives in `Type 0`. This is the real payoff
   over `Freer`: `Freer (Freer …)` does not type-check because of the universe bump (see
   the `#check_failure` in Layer 1), whereas `FreeM (P + Q)` does.

2. The carrier is ready to write programs in, not just a type to quantify over.
   `FreeM.liftA a` turns an operation name `a` into a one-step program that returns the
   operation's result `P.B a`, and `do`-notation sequences such steps. This is exactly how
   a concrete scheme's `prove` and `setup` are written. Here `x` comes from an operation of
   `P` (injected with `Sum.inl`) and `y` from one of `Q` (injected with `Sum.inr`),
   interleaved in one program. -/
example {P Q : SmallPFunctor} (a : P.A) (b : Q.A) :
    PFunctor.FreeM (P + Q) (P.B a × Q.B b) := do
  let x ← PFunctor.FreeM.liftA (P := P + Q) (Sum.inl a)
  let y ← PFunctor.FreeM.liftA (P := P + Q) (Sum.inr b)
  pure (x, y)

end Layer2

end KVAC.Core.NIZKP
