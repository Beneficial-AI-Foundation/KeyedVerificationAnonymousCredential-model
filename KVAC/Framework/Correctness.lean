/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Framework.Syntax
import KVAC.Core.NIZKP.Security
import VCVio.OracleComp.ProbComp

/-!
# Correctness of a keyed-verification credential system (O24 Definition 4.3)

`Correct` says: when both the issuance predicate `φ` and the presentation
predicate `φ'` hold on the attribute vector, honest issuance produces a
credential (no rejection, no abort) and honest presentation accepts it.

## Support-based form

Definition 4.3 asks the experiment to succeed with overwhelming probability;
like the MAC layer, we state the stronger support-based (probability-one)
form, which μCMZ satisfies perfectly. See
`KVAC/Core/AlgebraicMAC/Correctness.lean` for why the support form is the
lightest to prove.

This is strictly stronger than the paper's "overwhelming": a scheme with
negligible-but-nonzero correctness error would satisfy Definition 4.3 yet fail
`Correct`. That is fine for the perfectly-correct schemes we formalize; a
future scheme with correctness error would need a probabilistic restatement.

We split the paper's single experiment into its two halves — "issuance
completes" and "presentation accepts" — so downstream proofs, such as the
anonymity hybrids, can cite each on its own.

## Predicate-family scope

Definition 4.3 quantifies over a family containing all partial-disclosure
predicates `{φ_a⃗ : a⃗ ∈ (M ∪ {?})ⁿ}`, whereas the abstract `PredicateFamily`
guarantees only the trivial predicate and closure under conjunction
(Definition 4.1). This is deliberate: `Correct` is stated φ-generically
(`∀ φ φ'`), so it never needs the partial-disclosure predicates to exist. The
obligation to exhibit them is discharged by the concrete scheme's
predicate-family instance — μCMZ Figure 9, where `KVAC.M / KVAC.V` are actually
invoked — not by this abstract layer.

-- TODO: When a scheme instantiates `KVACSyntax` (μCMZ track), discharge O24
Definition 4.3's `φ ⊇ {φ_a⃗ : a⃗ ∈ (M ∪ {?})ⁿ}` clause: exhibit the
partial-disclosure predicates in that scheme's `PredicateFamily` instance and
show they lie in the family. This obligation is not visible to the abstract
`Correct` above and must not be lost.
-/

namespace KVAC.Framework

open OracleComp KVAC.Core

/--
The correctness conclusion of O24 Definition 4.3, factored out of both `Correct`
and `CorrectRO` and abstracted over how issuance and presentation outcomes are
drawn. `issued σ? s` holds when `σ?` is a possible issuance result carrying
auxiliary data `s` (the random-oracle cache at the `OracleComp (ZKRO H)` carrier,
`Unit` at `ProbComp`); `accepted σ s b` when `b` is a possible presentation bit
started from that `s`. The conclusion: issuance yields a credential and every
presentation under a satisfied `φ'` accepts. -/
def CorrectOutcome {Cr S : Type} (issued : Option Cr → S → Prop)
    (accepted : Cr → S → Bool → Prop) : Prop :=
  ∀ σ? s, issued σ? s → ∃ σ, σ? = some σ ∧ ∀ b, accepted σ s b → b = true

/--
How to execute a `KVACSyntax M` algorithm for the purposes of correctness: a
state type `S` with an initial state, and a relation `Runs c s a s'` meaning the
computation `c` can produce value `a`, taking the state `s → s'`. This is the one
thing that differs between the `ProbComp` and `OracleComp (ZKRO H)` carriers — at
`ProbComp` there is no oracle cache (`S = Unit`), at the oracle carrier `S` is the
random-oracle cache threaded by `runRO`. -/
structure RunSem (M : Type → Type) where
  /-- Auxiliary state threaded through the algorithms (the oracle cache, or `Unit`). -/
  S : Type
  /-- The initial state (empty cache, or `()`). -/
  init : S
  /-- `Runs c s a s'`: `c` may produce `a`, moving the state `s → s'`. -/
  Runs : {α : Type} → M α → S → α → S → Prop

/--
The O24 Definition 4.3 correctness skeleton, generic over a `RunSem`: run `setup`
from `init`, `keygen` from the state it leaves, then for every attribute vector
and every pair of predicates `φ, φ'` holding on it, the issuance and presentation
outcomes satisfy `CorrectOutcome`, with the post-issuance state threaded into
presentation. `Correct` and `CorrectRO` are this skeleton at the two carriers.

The `0 < n` hypothesis mirrors O24 Definition 4.2's requirement `n > 0`. -/
def GenCorrect {M : Type → Type} [Monad M] (sem : RunSem M)
    (kvac : KVACSyntax M) : Prop :=
  ∀ (secParam n : Nat), 0 < n →
  ∀ (crs : kvac.Crs secParam n) (s₀ : sem.S),
    sem.Runs (kvac.setup secParam n) sem.init crs s₀ →
  ∀ (keys : kvac.Sk crs × kvac.Pp crs) (s₁ : sem.S),
    sem.Runs (kvac.keygen crs) s₀ keys s₁ →
  ∀ (m : kvac.MsgVec crs) (φ φ' : kvac.Pred crs),
    kvac.holds crs φ m = true → kvac.holds crs φ' m = true →
    CorrectOutcome
      (fun σ? s₂ => sem.Runs (kvac.issue crs keys.1 keys.2 m φ) s₁ σ? s₂)
      (fun σ s₂ b =>
        ∃ s₃, sem.Runs (kvac.present crs keys.1 keys.2 m σ φ') s₂ b s₃)

/-- `ProbComp` run semantics: no oracle cache, `Runs c _ a _ := a ∈ support c`. -/
def probRunSem : RunSem ProbComp where
  S := Unit
  init := ()
  Runs := fun c _ a _ => a ∈ support c

/-- `OracleComp (ZKRO H)` run semantics: the random-oracle cache threaded by
`runRO`, `Runs c s a s' := (a, s') ∈ support (runRO H s c)`. -/
def roRunSem (H : HashSpec) : RunSem (OracleComp (ZKRO H)) where
  S := H.spec.QueryCache
  init := ∅
  Runs := fun c s a s' => (a, s') ∈ support (runRO H s c)

/--
Correctness (O24 Definition 4.3), support-based over `ProbComp`: honest issuance
under a satisfied `φ` always yields a credential and honest presentation under a
satisfied `φ'` always verifies. The `probRunSem` instance of `GenCorrect`. -/
def Correct (kvac : KVACSyntax ProbComp) : Prop :=
  GenCorrect probRunSem kvac

/--
Correctness lifted to the `OracleComp (ZKRO H)` carrier (issue #118): the same
`GenCorrect` skeleton, but with `setup`/`keygen`/`issue`/`present` run through the
shared random oracle via `runRO`, threading one cache `∅ → s₀ → s₁ → s₂ → s₃`, so
a Fiat–Shamir credential's proofs share the oracle. Mirrors
`KVAC.Core.PerfectlyComplete`. The `ProbComp` `Correct` is the oracle-free special
case, recovered through the `ProbComp ↪ OracleComp (ZKRO H)` lift. -/
def CorrectRO (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H))) : Prop :=
  GenCorrect (roRunSem H) kvac

end KVAC.Framework
