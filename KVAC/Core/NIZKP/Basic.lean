/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import Mathlib.Data.Set.Basic
import ToMathlib.PFunctor.Free

/-!
# A refinement approach for NIZKP specification

**Non-Interactive Zero-Knowledge Proof** (NIZKP) is a protocol where one party, the prover,
sends one message that must convince the other party in the protocol, the verifier, of a
statement without revealing nothing beyond its truth.

This refinement approach aims at defining a `NIZKP` that is _agnostic wrt the security model_.
This means that one may "plug" different security models into the abstract `NIZKP` and then
prove different security properties about the protocol.

The `NIZKPScheme` structure (`setup`/`prove`/`verify`/`relation`), together with the
properties `KnowledgeSound`, `SimulationExtractable`, and `ZeroKnowledge`, makes up the
abstract spec, parametric in an output carrier `F`. We keep `F` abstract rather than fixing it per
security model, so the ABSTRACT notions are defined once and specialize with no
reproof.

We refine over `F` in three different layers, as follows:

  0. `F` is an arbitrary type constructor.
  1. `F` is `Freer G`, a frer monad with the "freer" encoding. This decision
     follows the "Program is data." paradigm.
  2. `F` is `PFunctor.FreeM P`, a polynomial functor. It solves the so called
     "universe bump" that arises in level 1.

Reference: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint [2024/1552](https://eprint.iacr.org/2024/1552).

Note: In Orru's paper, `F` is left implicit as the paper tackles the computational
model only. Here, we aim at a specification that is agnostic wrt. the security model.
In the symbolic model `F Proof` is a _term_ over proofs. In the computational model, `F Proof`
is a _distribution_ over proofs.
-/

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
may use, such as sampling and oracle queries. -/

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
-- argument positively: `F` could be `fun X => X → Bool`, which would put
-- `Free F α` in a _negative_ position and the kernel rejects the definition.

-- The declaration below triggers exactly that rejection (its expected error is asserted):
-- error: (kernel) arg #3 of 'KVAC.Core.NIZKP.Free.roll' contains a non valid
-- occurrence of the datatypes being declared
-- (Note: rewrite the two lines above as a single line within /-- -/ and uncomment
--  the following 4 lines to see the errors.)
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
inductive Freer (F : Type u → Type u) (α : Type u) : Type (u + 1) where
  | pure (a : α) : Freer F α
  | bind {ι : Type u} (op : F ι) (k : ι → Freer F α) : Freer F α

/-- "Program is data" is now usable: a folder interprets the syntax. -/
protected def Freer.bindM : Freer F α → (α → Freer F β) → Freer F β
  | Freer.pure a,    g => g a
  | Freer.bind op k, g => Freer.bind op (fun x => Freer.bindM (k x) g)

instance : Monad (Freer F) where
  pure := Freer.pure
  bind := Freer.bindM

/-- The Layer-0 notions apply verbatim at the freer carrier — no restatement. -/
example {F : Type → Type} {Crs Stmt Witness Proof : Type}
    (nizkp : NIZKPScheme (Freer F) Crs Stmt Witness Proof) : Prop :=
  KnowledgeSound nizkp

-- However, remembering each operation's result type `ι` pushes the whole type up one universe up.
-- This is the so called "universe bump" problem.
-- The universe bump, made visible: `Freer.{u} : (Type u → Type u) → Type u →
-- Type (u+1)`. The codomain is `u+1`, not `u`.
-- set_option pp.universes true in
-- #check @Freer

-- The consequence of "universe bump" problem is *non-composability*.
-- `Freer` needs its base functor to be an endofunctor `Type u → Type u`. So a freer
-- monad cannot be composed with a freer monad: freer monads do not compose
-- under the bump.
-- #check_failure (Freer (Freer (fun _ : Type => Unit)))

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
as a fresh type argument, as in the Freer monad where each operation had to define its own ι.
Since no constructor quantifies over a type, nothing forces a level increase: `FreeM P` stays in
`Type 0`. Therefore free monads built this way compose. -/

section Layer2

variable {P : PFunctor.{0, 0}}

/-- `FreeM P : Type v → Type (max uA uB v)`; at `P.{0,0}, v = 0` that is
`Type 0`. So it genuinely IS a `Type → Type` endofunctor — no bump. -/
example (P : PFunctor.{0, 0}) : Type → Type := PFunctor.FreeM P

/-- The same notions, specialized again to the polynomial-functor carrier. -/
example {Crs Stmt Witness Proof : Type}
    (nizkp : NIZKPScheme (PFunctor.FreeM P) Crs Stmt Witness Proof) : Prop :=
  KnowledgeSound nizkp

/-- A handler `s` (interpret the syntax into a target monad `m` via `FreeM.mapM`)
*induces* a `SecurityModel`: both model relations are refined to handler-based ones —
interpret, then compare — rather than rewritten. -/
def handlerModel {m : Type → Type} [Monad m] (s : (a : P.A) → m (P.B a)) :
    SecurityModel (PFunctor.FreeM P) where
  Indist a b := a.mapM s = b.mapM s
  produces c a := c.mapM s = pure a

/-- Under that induced model, the Layer-0 `ZeroKnowledge` applies unchanged. -/
example {Crs Stmt Witness Proof : Type} {m : Type → Type} [Monad m]
    (s : (a : P.A) → m (P.B a))
    (nizkp : NIZKPScheme (PFunctor.FreeM P) Crs Stmt Witness Proof) : Prop :=
  letI := handlerModel s
  ZeroKnowledge nizkp

end Layer2

end KVAC.Core.NIZKP
