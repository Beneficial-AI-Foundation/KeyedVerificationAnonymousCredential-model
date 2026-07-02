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
`indist`, `produces`, and `extracts`, so the abstract notions specialize to each model with no
reproof. The concrete carrier is the free monad on a polynomial functor, `PFunctor.FreeM P`,
on which the concrete schemes are built.

TODO. The refinement that motivates this carrier, from an arbitrary `F` through the freer encoding
to the polynomial-functor free monad, will be documented in the Blueprint.

## Consistency of the specification with respect to the paper

- What matches O24. The `NIZKPScheme` fields are the three algorithms (`setup`, `prove`, `verify`)
  and the relation family of §3.3. The properties follow §3.3, with simulation-extractability
  following the definition O24 cites (Dao–Grubbs, ePrint 2023/494). Each property ranges only over
  honestly generated CRSes (`produces (setup secParam) crs`), and simulation-extractability uses one
  simulator for both zero-knowledge and extraction, both as in the paper.

- What is abstracted. O24 fixes the computational model. Here, `F` and the `SecurityModel` relations
  stay abstract, so the quantitative, asymptotic content (advantage, negligibility in λ) lives in
  the computational refinement, not here.
  * `F` is explicit. `F Proof` is a term in the symbolic model, a distribution in the computational
    model.
  * `indist`, in `ZeroKnowledge`, relates a single pair of outputs, not a negligible advantage over
    an adaptive, multi-query game.
  * `extracts`, in `KnowledgeSound` and `SimulationExtractable`, is the model-supplied extraction
    relation, not the paper's efficient extractor over the prover's coins and code.
  * `produces`, the freshness guard in `SimulationExtractable`, marks the proofs a simulator could
    output, not a run-time log of issued proofs.

Reference. Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint [2024/1552](https://eprint.iacr.org/2024/1552). -/

namespace KVAC.Core.NIZKP

/-! ## The abstract specification over a carrier `F` -/

section AbstractSpec

variable {F : Type → Type} [Pure F] {Crs Stmt Witness Proof : Type}

structure NIZKPScheme (F : Type → Type) (Crs Stmt Witness Proof : Type) where
  /-- `S(1^secParam)` is setup on the security parameter. It outputs a CRS and implicitly selects
  a relation (O24 §3.3, algorithm `ZKP.S`). -/
  setup : (secParam : Nat) → F Crs
  /-- `P(crs, x, w)` is the prover. From a witnessed instance it produces a proof
  (O24 §3.3, algorithm `ZKP.P`). -/
  prove : Crs → Stmt → Witness → F Proof
  /-- `V(crs, x, π)` is the verifier as an `F`-computation producing `true`/`false` for accept
  or reject. Being `F`-valued, an oracle-querying verifier such as a Fiat–Shamir verifier
  recomputing `c = H(a, x)` fits the API (O24 §3.3, algorithm `ZKP.V`). -/
  verify : Crs → Stmt → Proof → F Bool
  /-- `relation crs x w` says `w` witnesses `x` under the relation that `setup` selects
  (O24 §3.3). The leading `Crs →` is O24's crs-indexing. It is a field, so the security
  properties read it from the scheme as `relation crs`. -/
  relation : Crs → Stmt → Witness → Prop

/-- A security model for the carrier `F` provides the model-dependent relations `indist`,
`produces`, and `extracts` that the security properties read, with the laws every model satisfies.
The laws are anchored on the deterministic computations `pure a`, so the class requires `[Pure F]`,
and they keep each relation non-degenerate, so an instance cannot be vacuous. -/
class SecurityModel (F : Type → Type) [Pure F] where
  /-- Indistinguishability of two `F`-computations, used by `ZeroKnowledge`. -/
  indist : ∀ {α : Type}, F α → F α → Prop
  /-- `produces c a` holds when `a` is a possible output of the computation `c`. -/
  produces : ∀ {α : Type}, F α → α → Prop
  /-- `indist` is reflexive. -/
  indist_refl : ∀ {α} (a : F α), indist a a
  /-- `indist` is symmetric. -/
  indist_symm : ∀ {α} {a b : F α}, indist a b → indist b a
  /-- Distinct deterministic computations are distinguishable. This rules out the total relation
  `fun _ _ => True`, since distinct constants are told apart in every model. -/
  indist_separates_pure : ∀ {α} {a b : α}, a ≠ b → ¬ indist (pure a) (pure b)
  /-- A deterministic computation produces exactly its value. Rules out both `fun _ _ => True`
  and `fun _ _ => False` for `produces`. -/
  produces_pure : ∀ {α} (a b : α), produces (pure a) b ↔ a = b
  /-- `extracts c w` holds when witness `w` can be extracted from the computation `c`. This
  model-dependent knowledge relation is symbolic derivation from the proof term or the computational
  extractor, kept non-degenerate by the two laws below. -/
  extracts : ∀ {α β : Type}, F α → β → Prop
  /-- A value is extractable from its own deterministic computation. Extraction is therefore
  non-vacuous, which rules out the empty relation `fun _ _ => False`. -/
  extracts_pure_self : ∀ {α} (a : α), extracts (pure a) a
  /-- Extraction is partial. Some value is not extractable from some computation, which rules out
  the total relation `fun _ _ => True`. The non-extractable computations are the fake proofs, which
  the proof type holds alongside the real ones. -/
  extracts_partial : ∃ (α : Type) (c : F α) (a : α), ¬ extracts c a

/-- Knowledge soundness. For an honestly generated CRS, every accepting proof yields a witness that
extracts from it. The CRS scope is `produces (setup secParam) crs`, acceptance is
`produces (verify …) true`, and extraction is `extracts`, all from the `SecurityModel`. The witness
must come from the proof, so this is stronger than language soundness. -/
def KnowledgeSound [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∀ secParam crs x π, SecurityModel.produces (nizkp.setup secParam) crs →
    SecurityModel.produces (nizkp.verify crs x π) true →
      ∃ w, nizkp.relation crs x w ∧ SecurityModel.extracts (pure π : F Proof) w

/-- Zero-knowledge for a given simulator `sim`. For an honestly generated CRS, `sim` produces from
the statement alone something `indist` from the real prover's output. `indist` comes from the
`SecurityModel`, equal terms symbolically and negligible advantage computationally. `sim` is a
parameter, not bound here, so it is shared with simulation-extractability. -/
def ZeroKnowledge [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) (sim : Crs → Stmt → F Proof) : Prop :=
  ∀ secParam crs x w, SecurityModel.produces (nizkp.setup secParam) crs →
    nizkp.relation crs x w →
      SecurityModel.indist (nizkp.prove crs x w) (sim crs x)

/-- Extraction for a given simulator `sim`. For an honestly generated CRS, every accepting proof
that `sim` did not produce is real and a witness extracts from it. A proof is fake when
`produces (sim crs x) π` holds, and nothing extracts from a fake. Internal building block of
`SimulationExtractable`. -/
def Extractable [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) (sim : Crs → Stmt → F Proof) : Prop :=
  ∀ secParam crs x π, SecurityModel.produces (nizkp.setup secParam) crs →
    SecurityModel.produces (nizkp.verify crs x π) true →
    ¬ SecurityModel.produces (sim crs x) π →
      ∃ w, nizkp.relation crs x w ∧ SecurityModel.extracts (pure π : F Proof) w

/-- Simulation-extractability (O24 §3.3, via Dao–Grubbs). One simulator gives both zero-knowledge
and extraction, matching the paper's single existential over the simulator. -/
def SimulationExtractable [SecurityModel F]
    (nizkp : NIZKPScheme F Crs Stmt Witness Proof) : Prop :=
  ∃ sim : Crs → Stmt → F Proof, ZeroKnowledge nizkp sim ∧ Extractable nizkp sim

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
concrete schemes are built on this carrier. The refinement that leads here is in the
Blueprint. -/

section FreeMonadSpec

/-- A polynomial functor whose operation names and result types are all small (`Type 0`), so
`PFunctor.FreeM P : Type → Type`. -/
abbrev SmallPFunctor := PFunctor.{0, 0}

variable {P : SmallPFunctor}

/-- A NIZKP scheme over the free monad on the effect signature `P`. This is the form the
concrete schemes (μCMZ, μBBS) are built on. `P` names the operations a proof may use,
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

1. Effect signatures compose by the sum `+` (VCV-io's `PFunctor.sum`). The operation names
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
