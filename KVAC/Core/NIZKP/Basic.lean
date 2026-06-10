/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import ToMathlib.PFunctor.Free

/-!
# NIZKP specification, agnostic with respect to the security model

A non-interactive zero-knowledge proof (NIZKP) lets a prover convince a verifier of a
statement with a single message, revealing nothing beyond its truth.

The specification is agnostic with respect to the security model. The `NIZKPScheme`
structure (`setup`, `prove`, `verify`, `relation`) and the properties `KnowledgeSound`,
`SimulationExtractable`, and `ZeroKnowledge` are stated once over an abstract carrier
`F : Type → Type`. A `SecurityModel F` instance supplies the model-dependent relations
`indist` and `produces`, so the abstract notions specialize to each model with no reproof.
The concrete carrier is the free monad on a polynomial functor, `PFunctor.FreeM P`, against
which the concrete schemes are built.

The refinement that motivates this carrier, from an arbitrary `F` through the freer encoding
to the polynomial-functor free monad, is documented in the Blueprint.

## Consistency of the specification with respect to the paper

- What is consistent. The `NIZKPScheme` fields match the three algorithms and the relation
  family of O24 §3.3. The properties follow the same section, and simulation-extractability
  follows the definition O24 points to (Dao–Grubbs, ePrint 2023/494).

- Where the spec differs. The paper works only in the computational model, so the abstract
  spec omits that machinery:
  * `KnowledgeSound` and `SimulationExtractable` are relational: an accepting proof must be a
    possible honest output of `prove` for a valid witness (honest-image soundness), not a
    witness recovered by an efficient extractor from the prover's code and coins.
  * `indist`, in `ZeroKnowledge`, compares a single pair of outputs, not a negligible
    advantage over many queries.
  * `produces`, in `SimulationExtractable`, marks the proofs a simulator could output, not a
    running record of issued proofs.
  * Completeness is left to the security model, since whether a proof verifies depends on the
    model; there is no `Complete` at the abstract layer.
  * `F` is explicit here: `F Proof` is a term in the symbolic model and a distribution in the
    computational model.

Reference: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint [2024/1552](https://eprint.iacr.org/2024/1552). -/

-- TODO: project documentation, including the refinement tower (the freer-monad encoding) and
-- its Blueprint rendering, will be produced in a later PR.

namespace KVAC.Core.NIZKP

/-! ## The abstract specification over a carrier `F` -/

section AbstractSpec

variable {F : Type → Type} [Pure F] {Crs Stmt Witness Proof : Type}

structure NIZKPScheme (F : Type → Type) (Crs Stmt Witness Proof : Type) where
  /-- `S(1^secParam)`: setup on the security parameter; outputs a CRS and implicitly selects
  a relation (O24 §3.3, algorithm `ZKP.S`). -/
  setup : (secParam : Nat) → F Crs
  /-- `P(crs, x, w)`: prover; from a witnessed instance produces a proof
  (O24 §3.3, algorithm `ZKP.P`). -/
  prove : Crs → Stmt → Witness → F Proof
  /-- `V(crs, x, π)`: verifier as an `F`-computation producing `true`/`false` for
  accept/reject. Being `F`-valued, an oracle-querying verifier such as a Fiat–Shamir
  verifier recomputing `c = H(a, x)` fits the API (O24 §3.3, algorithm `ZKP.V`). -/
  verify : Crs → Stmt → Proof → F Bool
  /-- `relation crs x w`: `w` witnesses `x` under the relation that `setup` selects
  (O24 §3.3). The leading `Crs →` is O24's crs-indexing. It is a field, so the security
  properties read it from the scheme as `relation crs`. -/
  relation : Crs → Stmt → Witness → Prop

/-- A security model for the carrier `F`: the model-dependent relations the security
properties are stated against, together with the laws every model satisfies. Requires
`[Pure F]`, since the laws are anchored on the deterministic computations `pure a`. The laws
make the degenerate relations uninhabitable, so a `SecurityModel` instance is lawful by
construction. -/
class SecurityModel (F : Type → Type) [Pure F] where
  /-- Indistinguishability of two `F`-computations (used by `ZeroKnowledge`). -/
  indist : ∀ {α : Type}, F α → F α → Prop
  /-- `produces c a` holds when `a` is a possible output of the computation `c`. -/
  produces : ∀ {α : Type}, F α → α → Prop
  /-- `indist` is reflexive. -/
  indist_refl : ∀ {α} (a : F α), indist a a
  /-- `indist` is symmetric. -/
  indist_symm : ∀ {α} {a b : F α}, indist a b → indist b a
  /-- Distinct deterministic computations are distinguishable. Rules out the total relation
  `fun _ _ => True` in every model, since distinct constants always carry maximal advantage. -/
  indist_separates_pure : ∀ {α} {a b : α}, a ≠ b → ¬ indist (pure a) (pure b)
  /-- A deterministic computation produces exactly its value. Rules out both `fun _ _ => True`
  and `fun _ _ => False` for `produces`. -/
  produces_pure : ∀ {α} (a b : α), produces (pure a) b ↔ a = b

/-- Knowledge soundness: every accepting proof is real, that is, a possible honest output of
`prove` for some valid witness. "Accepts" is `produces (verify …) true` and "real" is
`produces (prove crs x w) π`, both from the `SecurityModel`. The witness is recovered through
`prove`, not an extractor function, so the statement does not collapse to plain language
soundness (`∃ w, relation crs x w`); the `produces (prove …) π` conjunct rules out forgeries
no honest prover could make. An efficient extractor over the prover's coins is the
computational game layer, not this relational form. -/
def KnowledgeSound [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∀ crs x π, SecurityModel.produces (nizkp.verify crs x π) true →
    ∃ w, nizkp.relation crs x w ∧ SecurityModel.produces (nizkp.prove crs x w) π

/-- Zero-knowledge against a given simulator `sim`: knowing only the statement, `sim`
produces something `indist` from the real prover's output. `indist` comes from the
`SecurityModel`: equality of terms in the symbolic model, negligible advantage in the
computational model. The simulator is a parameter, not existentially bound here, so the same
`sim` can be shared with simulation-extractability. -/
def ZeroKnowledge [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) (sim : Crs → Stmt → F Proof) : Prop :=
  ∀ crs x w, nizkp.relation crs x w →
    SecurityModel.indist (nizkp.prove crs x w) (sim crs x)

/-- Extraction against a given simulator `sim`: every accepting proof that `sim` did not
produce is real, that is, a possible honest output of `prove` for some valid witness. "Real"
is `produces (prove crs x w) π`, "fake" is `produces (sim crs x) π`, both from the
`SecurityModel`. The witness is recovered through `prove`, not an extractor function, so the
statement does not collapse to plain language soundness. -/
def ExtractsAgainst [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) (sim : Crs → Stmt → F Proof) : Prop :=
  ∀ crs x π, SecurityModel.produces (nizkp.verify crs x π) true →
    ¬ SecurityModel.produces (sim crs x) π →
      ∃ w, nizkp.relation crs x w ∧ SecurityModel.produces (nizkp.prove crs x w) π

/-- Simulation-extractability (O24 §3.3, via Dao–Grubbs). The same simulator is used
in zero-knowledge and extraction, matching the paper's single existential over the simulator. -/
def SimulationExtractable [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∃ sim : Crs → Stmt → F Proof, ZeroKnowledge nizkp sim ∧ ExtractsAgainst nizkp sim

/-- Makes explicit that simulation-extractability gives zero-knowledge for the same simulator. -/
theorem SimulationExtractable.toZeroKnowledge [SecurityModel F]
    {nizkp : NIZKPScheme F Crs Stmt Witness Proof} (h : SimulationExtractable nizkp) :
    ∃ sim, ZeroKnowledge nizkp sim :=
  ⟨h.choose, h.choose_spec.1⟩

end AbstractSpec

/-! ## The free-monad carrier `PFunctor.FreeM P`

Cryptographically, the carrier is the model of computation the algorithms run in.
The concrete carrier in this section is the free monad on a polynomial functor `P`, a pair of
operation names `P.A` and result types `P.B`. A `FreeM P` program names operations without
quantifying over a fresh result type, so it stays in `Type 0` and composes under the sum `+`. The
concrete schemes are built against this carrier. The refinement that leads here is in the
Blueprint. -/

section FreeMonadSpec

/-- A polynomial functor whose operation names and result types are all small (`Type 0`), so
`PFunctor.FreeM P : Type → Type`. -/
abbrev SmallPFunctor := PFunctor.{0, 0}

variable {P : SmallPFunctor}

/-- A NIZKP scheme over the free monad on the effect signature `P`. This is the form the
concrete schemes (μCMZ, μBBS) are built against: `P` names the operations a proof may use,
composed with `+`. Being an `abbrev`, every abstract property applies to it unchanged. -/
abbrev FreeNIZKPScheme (P : SmallPFunctor) (Crs Stmt Witness Proof : Type) :=
  NIZKPScheme (PFunctor.FreeM P) Crs Stmt Witness Proof

/-- `PFunctor.FreeM P` is genuinely a `Type → Type` endofunctor, with no universe bump. -/
example (P : SmallPFunctor) : Type → Type := PFunctor.FreeM P

/-- The abstract notions apply verbatim at the free-monad carrier, with no restatement. -/
example {Crs Stmt Witness Proof : Type} [SecurityModel (PFunctor.FreeM P)]
    (nizkp : FreeNIZKPScheme P Crs Stmt Witness Proof) : Prop :=
  KnowledgeSound nizkp

/-- Under any security model on the carrier, `SimulationExtractable` applies unchanged. -/
example {Crs Stmt Witness Proof : Type} [SecurityModel (PFunctor.FreeM P)]
    (nizkp : FreeNIZKPScheme P Crs Stmt Witness Proof) : Prop :=
  SimulationExtractable nizkp

/-- This example witnesses the two things that make this the usable carrier.

1. Effect signatures compose by the sum `+` (VCV-io's `PFunctor.sum`): the operation names
   become `P.A ⊕ Q.A` and each keeps its own result type. Both signatures lift into one free
   monad `FreeM (P + Q)`, which still lives in `Type 0`.

2. The carrier is ready to write programs in, not just a type to quantify over.
   `FreeM.liftA a` turns an operation name `a` into a one-step program returning the
   operation's result `P.B a`, and `do`-notation sequences such steps. This is how a concrete
   scheme's `prove` and `setup` are written. Here `x` comes from an operation of `P` (injected
   with `Sum.inl`) and `y` from one of `Q` (injected with `Sum.inr`). -/
example {P Q : SmallPFunctor} (a : P.A) (b : Q.A) :
    PFunctor.FreeM (P + Q) (P.B a × Q.B b) := do
  let x ← PFunctor.FreeM.liftA (P := P + Q) (Sum.inl a)
  let y ← PFunctor.FreeM.liftA (P := P + Q) (Sum.inr b)
  pure (x, y)

end FreeMonadSpec

end KVAC.Core.NIZKP
