/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.NIZKP.Basic
import VCVio.OracleComp.EvalDist

/-!
# The computational security model for NIZKP

`Core/NIZKP/Basic.lean` keeps the carrier `F` abstract and states the security properties
`KnowledgeSound`, `ZeroKnowledge`, and `SimulationExtractable` against a `SecurityModel` class
that supplies two model-dependent relations, `Indist` and `produces`. This file is the
*computational* instance of that class. Here, `F Proof` is a distribution over proofs.

## VCV-io's `OracleComp` in brief

`OracleComp spec α` is VCV-io's type of probabilistic computations: a *program* that returns a
value of type `α` and may, along the way, call the oracles `spec` names.

The signature `spec` is a *catalogue of oracles*. Its type is a function from labels to types,

  `def OracleSpec (ι : Type) := ι → Type`,

read as:
  - each label `t : ι` is the name of one oracle, or equivalently one *operation* the program may
    perform;
  - `spec t` is the range of the operator named `t`.

A `PFunctor` is a pair of operation names `A : Type` and a result-type family `B : A → Type`.
`spec.toPFunctor` turns the catalogue into one by renaming its two fields:
```
  def toPFunctor (spec : OracleSpec ι) : PFunctor := { A := ι, B := spec }
```
So the operation names `A` are the labels `ι`, and the result type `B t` of operation `t` is the
answer type `spec t`. VCV-io then defines `OracleComp spec` as the free monad over that polynomial
functor:
```
  def OracleComp {ι : Type u} (spec : OracleSpec.{u,v} ι) :
      Type w → Type (max u v w) :=
    PFunctor.FreeM spec.toPFunctor
```

Here is the mapping between oracle elements and free-monad elements:

  ┌────────────────────────────────┬───────────────────────────────┐
  │      free monad (FreeM P)      │ oracle view (OracleComp spec) │
  ├────────────────────────────────┼───────────────────────────────┤
  │ operation name a : P.A         │ oracle label t : ι            │
  ├────────────────────────────────┼───────────────────────────────┤
  │ result type P.B a              │ answer type spec t            │
  ├────────────────────────────────┼───────────────────────────────┤
  │ one-step program FreeM.liftA a │ query t                       │
  └────────────────────────────────┴───────────────────────────────┘

A program `OracleComp spec α` is like any monadic value: `pure a` returns immediately,
`query t` performs one oracle call yielding an answer in `spec t`, and `do`-notation sequences
these steps. The program is pure syntax and computes nothing by itself. An *interpretation* gives
it meaning, and the computational model uses two of them, each taking a computation
`c : OracleComp spec α`:

- `support c : Set α`: the set of values `c` can return; available for any `spec`.
- `evalDist c : SPMF α`: the output distribution from answering each query uniformly at random
  over its range.

The computational `SecurityModel` builds `produces` and `Indist` relations from these two
interpretations.

## `FreeNIZKPScheme` and `OracleComp`

`OracleComp spec` is the standard object that game-based cryptography reasons about. Note that this
is not a new shape. As the definition above shows, it is the Layer-2 free monad of `Basic.lean`,
with polynomial functor `spec.toPFunctor`. A computational `NIZKPScheme` over `OracleComp spec` is
therefore, a special case of `FreeNIZKPScheme`, namely `FreeNIZKPScheme spec.toPFunctor`.
We designed the abstract spec and the two refinement layers so that this instance needs no new
carrier: the computational model is already a special case of the Layer-2 free monad. Verifying
this is the architectural point this file checks.

The two relations:

- `produces c a` is membership in the *support* of the computation: `a` is a value `c` can
  return with non-zero probability. This is the computational reading that `Basic.lean` announces,
  namely that `a` lies in the support of `c`. It needs no extra assumption on `spec`.

- `Indist a b` is equality of the *induced distributions*: `evalDist a = evalDist b`. Two
  computations are indistinguishable when they produce the same sub-distribution over outputs.
  Computing `evalDist` requires each oracle to have a finite, inhabited range, so the instance
  assumes `spec.Fintype` and `spec.Inhabited`.

## What this captures, and what it defers

The abstract relation `Indist : F α → F α → Prop` compares a single pair of computations. It
carries no security parameter `λ`. So the notion definable at this signature is *perfect*
indistinguishability: the two distributions are literally equal. It is not the asymptotic
"distinguishing advantage is negligible in `λ`" of O24. We do not lose that asymptotic,
quantitative notion: it belongs to the game-based security definitions, VCV-io's `SecurityExp`
and `SecurityGame`. These are phrased as advantage functions over `λ`-indexed families, and they
consume the proof system as a component. We deliberately keep the qualitative `SecurityModel`
predicates separate from the game-based, quantitative definitions.

Perfect indistinguishability is also the right fit for the intended use: O24 notes that
`µCMZ[ZKP = Σ]` has *statistical* anonymity when `Σ` is statistically knowledge-sound, so the
equality-of-distributions reading of zero-knowledge is the one that applies there.

Reference: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint [2024/1552](https://eprint.iacr.org/2024/1552). -/

namespace KVAC.Core.NIZKP

open OracleComp

variable {ι : Type} {spec : OracleSpec ι}

/-- The computational security model on the carrier `OracleComp spec`:
- `produces c a` := `a` is a possible output of `c`, a member of its support;
- `Indist a b` := `a` and `b` induce the same output distribution, perfect indistinguishability.

`produces` alone needs no assumption on `spec`; `Indist` uses `evalDist`, which requires each
oracle range to be finite and inhabited.

Limitation. Equality of distributions is the strongest, perfect notion. A single `OracleComp spec`
value carries no security parameter, so `Indist` cannot express O24's asymptotic notion, where the
distinguishing advantage is negligible in the security parameter. At this instance `ZeroKnowledge`
means perfect zero-knowledge. That asymptotic notion lives in the separate game-based security
definitions, which thread the security parameter through `setup`. It is not expressible through
this `Indist`. -/
noncomputable instance computationalModel [spec.Fintype] [spec.Inhabited] :
    SecurityModel (OracleComp spec) where
  Indist a b := evalDist a = evalDist b
  produces c a := a ∈ support c

/-! ## The instance is meaningful

A few small facts to confirm the two relations behave as intended, rather than being vacuous. -/

/-- `produces` recognizes the output of a finished computation: `pure a` produces `a`. -/
example [spec.Fintype] [spec.Inhabited] (a : α) :
    SecurityModel.produces (pure a : OracleComp spec α) a := by
  simp [SecurityModel.produces]

/-- `Indist` is reflexive: every computation is indistinguishable from itself. -/
example [spec.Fintype] [spec.Inhabited] (c : OracleComp spec α) :
    SecurityModel.Indist c c := by
  simp [SecurityModel.Indist]

/-! ## The architectural check

The point of keeping `F` abstract in `Basic.lean` is that the Layer-0 security properties apply
to *any* carrier with a `SecurityModel`, with no restatement. The following witness that they
resolve at the computational carrier through `computationalModel`. The symbolic and computational
models share one set of definitions. -/

/-- `KnowledgeSound`, which needs no `SecurityModel`, applies at the computational carrier. -/
example [spec.Fintype] [spec.Inhabited] {Crs Stmt Witness Proof : Type}
    (nizkp : NIZKPScheme (OracleComp spec) Crs Stmt Witness Proof) : Prop :=
  KnowledgeSound nizkp

/-- `ZeroKnowledge` resolves its `SecurityModel` to the computational one. -/
example [spec.Fintype] [spec.Inhabited] {Crs Stmt Witness Proof : Type}
    (nizkp : NIZKPScheme (OracleComp spec) Crs Stmt Witness Proof) : Prop :=
  ZeroKnowledge nizkp

/-- `SimulationExtractable` resolves its `SecurityModel` to the computational one. -/
example [spec.Fintype] [spec.Inhabited] {Crs Stmt Witness Proof : Type}
    (nizkp : NIZKPScheme (OracleComp spec) Crs Stmt Witness Proof) : Prop :=
  SimulationExtractable nizkp

/-- The computational scheme is literally a Layer-2 scheme: `OracleComp spec` is
`PFunctor.FreeM spec.toPFunctor`, so a computational `NIZKPScheme` is a `FreeNIZKPScheme`
over the oracle signature's polynomial functor. -/
example {Crs Stmt Witness Proof : Type}
    (nizkp : FreeNIZKPScheme spec.toPFunctor Crs Stmt Witness Proof) :
    NIZKPScheme (OracleComp spec) Crs Stmt Witness Proof :=
  nizkp

end KVAC.Core.NIZKP
