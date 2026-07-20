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

We split the paper's single experiment into its two halves — "issuance
completes" and "presentation accepts" — so downstream proofs, such as the
anonymity hybrids, can cite each on its own.
-/

namespace KVAC.Framework

open OracleComp

/--
Correctness (O24 Definition 4.3), support-based: for every CRS from `setup`,
every key pair from `keygen`, every attribute vector, and all predicates
`φ, φ'` holding on it, honest issuance under `φ` always yields a credential
and honest presentation under `φ'` always verifies.
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

end KVAC.Framework
