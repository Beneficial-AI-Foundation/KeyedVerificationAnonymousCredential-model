/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Framework.Syntax
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

open OracleComp

/--
Correctness (O24 Definition 4.3), support-based: for every CRS from `setup`,
every key pair from `keygen`, every attribute vector, and all predicates
`φ, φ'` holding on it, honest issuance under `φ` always yields a credential
and honest presentation under `φ'` always verifies.

The `0 < n` hypothesis mirrors O24 Definition 4.2's requirement that the
attribute count `n > 0`.
-/
def Correct (kvac : KVACSyntax ProbComp) : Prop :=
  ∀ (secParam n : Nat), 0 < n →
  ∀ (crs : kvac.Crs secParam n), crs ∈ support (kvac.setup secParam n) →
  ∀ (keys : kvac.Sk crs × kvac.Pp crs), keys ∈ support (kvac.keygen crs) →
  ∀ (m : kvac.MsgVec crs) (φ φ' : kvac.Pred crs),
    kvac.holds crs φ m = true → kvac.holds crs φ' m = true →
    (∀ σ? ∈ support (kvac.issue crs keys.1 keys.2 m φ),
      ∃ σ, σ? = some σ ∧
        ∀ b ∈ support (kvac.present crs keys.1 keys.2 m σ φ'), b = true)

end KVAC.Framework
