/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.KeyedSetup

/-!
# Credential predicate family (O24 Definition 4.1)

A credential predicate is an efficiently-computable Boolean test on attribute
vectors; a predicate family is a non-empty set of such predicates containing
the trivial predicate and closed under conjunction, following Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
(O24), Definition 4.1.

Predicates are *data*: they are inputs to the issuance/presentation algorithms
and the statements of the attached zero-knowledge proofs. So the family is a
structure carrying a per-CRS type `Pred` with its Boolean semantics `holds`,
together with the two closure properties of Definition 4.1 — a trivial
predicate and conjunction — as fields.

## Layering

`PredicateFamily` extends `KeyedSetupSyntax` (`KVAC.Core.KeyedSetup`) rather
than standing alone: O24 Definition 4.2 has the setup `crs ← S(1^λ, n)`
*implicitly define both* the attribute space `M` and the predicate family `Φ`,
so `Pred`/`holds` are typed against the very `Crs`/`Msg` that `KeyedSetupSyntax`
introduces. `KVACSyntax` (Definition 4.2) then extends this with the issuance
and presentation algorithms, giving the tower

```
KeyedSetupSyntax  ⊆  PredicateFamily  ⊆  KVACSyntax
   (crs, keys)        (+ Def 4.1 Φ)      (+ Def 4.2 I/P)
```
-/

namespace KVAC.Framework

open KVAC.Core

/--
A credential predicate family over a keyed setup (O24 Definition 4.1): the
per-CRS type of predicate descriptions `Pred`, their Boolean semantics
`holds`, and the closure properties every family enjoys — it contains the
trivial predicate and is closed under conjunction. Monad-polymorphic only
because it extends `KeyedSetupSyntax M`; the family fields themselves are pure.
-/
structure PredicateFamily (M : Type → Type) [Monad M]
    extends KeyedSetupSyntax M where
  /-- Predicate descriptions `φ ∈ Φ`, selected by the CRS. Predicates are data
  because they are inputs to issuance and presentation. -/
  Pred : {secParam n : Nat} → Crs secParam n → Type
  /-- Boolean semantics of a predicate on an attribute vector: O24's
  `φ(m⃗) ∈ {0,1}` (efficiently computable, hence `Bool`). -/
  holds : {secParam n : Nat} → (crs : Crs secParam n) → Pred crs →
    (Fin n → Msg crs) → Bool
  /-- The trivial predicate `φ₁` that every attribute vector satisfies
  (O24 Definition 4.1: every family contains it). -/
  trivialPred : {secParam n : Nat} → (crs : Crs secParam n) → Pred crs
  /-- `φ₁` accepts everything. -/
  holds_trivialPred : ∀ {secParam n : Nat} (crs : Crs secParam n)
    (m : Fin n → Msg crs), holds crs (trivialPred crs) m = true
  /-- Conjunction of predicates (O24 Definition 4.1: families are closed
  under conjunction). -/
  andPred : {secParam n : Nat} → (crs : Crs secParam n) → Pred crs →
    Pred crs → Pred crs
  /-- `andPred` is semantic conjunction. -/
  holds_andPred : ∀ {secParam n : Nat} (crs : Crs secParam n)
    (φ φ' : Pred crs) (m : Fin n → Msg crs),
    holds crs (andPred crs φ φ') m = (holds crs φ m && holds crs φ' m)

end KVAC.Framework
