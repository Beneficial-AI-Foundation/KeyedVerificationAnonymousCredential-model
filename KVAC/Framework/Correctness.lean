/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.Credential.Syntax
import VCVio.OracleComp.ProbComp

/-!
# Correctness of a keyed-verification credential system (O24 Definition 4.3)

Correctness predicate `Correct` on a `KVACSyntax ProbComp`: whenever the
issuance predicate `φ` and the presentation predicate `φ'` both hold on the
attribute vector, the honest issuance protocol produces a credential (no
rejection, no abort) and the honest presentation protocol accepts it.

## Support-based (perfect) form

O24 Definition 4.3 asks that the composed experiment succeed with
*overwhelming* probability; as with the MAC layer we state the stronger
support-based (probability-one) form, which the schemes we formalize (μCMZ)
satisfy perfectly — see `KVAC/Core/AlgebraicMAC/Correctness.lean` for the
discussion of the equivalent formulations and why the support form is the
lightest to prove.

The statement splits the paper's single experiment into its two halves,
quantifying over the support at each protocol boundary:

1. **Issuance completes:** every output of `kvac.issue` is `some σ`.
2. **Presentation accepts:** for every issued `σ`, every output of
   `kvac.present` is `true`.

This is equivalent to "the composed experiment returns `1`" but gives the
two facts separately, which downstream proofs (the anonymity hybrids need
"issuance completes" on the honest side) can cite individually.
-/

namespace KVAC.Core

open OracleComp

/--
Correctness for a keyed-verification credential system (O24 Definition 4.3),
support-based: for every CRS in the support of `setup`, every key pair in
the support of `keygen`, every attribute vector `m⃗`, and all predicates
`φ, φ'` holding on `m⃗`, honest issuance under `φ` always yields a
credential, and honest presentation of that credential under `φ'` always
verifies.
-/
def KVACSyntax.Correct (kvac : KVACSyntax ProbComp) : Prop :=
  ∀ (secParam n : Nat),
  ∀ (crs : kvac.Crs secParam n), crs ∈ support (kvac.setup secParam n) →
  ∀ (keys : kvac.Sk crs × kvac.Pp crs), keys ∈ support (kvac.keygen crs) →
  ∀ (m : kvac.MsgVec crs) (φ φ' : kvac.Pred crs),
    kvac.holds crs φ m = true → kvac.holds crs φ' m = true →
    (∀ σ? ∈ support (kvac.issue crs keys.1 keys.2 m φ),
      ∃ σ, σ? = some σ ∧
        ∀ b ∈ support (kvac.present crs keys.1 keys.2 m σ φ'), b = true)

end KVAC.Core
