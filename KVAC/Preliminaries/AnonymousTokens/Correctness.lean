/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Preliminaries.AnonymousTokens.Construction
import VCVio.OracleComp.ProbComp

/-!
# Correctness of an anonymous-token scheme (O24 §3.4)

`Correct` renders O24 §3.4's "all tokens generated via `AT.I.{Usr, Srv}`
for messages in the family successfully verify", in the support-based
(probability-one) form the repo uses for its perfectly-correct schemes —
the same convention as `KVAC.Core.Correct` and `KVAC.Framework.Correct`.
-/

namespace KVAC.Preliminaries

open OracleComp

namespace ATSyntax

/--
Correctness of an anonymous-token scheme, support-based: for every CRS
from `setup`, every key pair from `keygen`, and every attribute vector,
honest issuance always yields a token and that token always verifies.

The `0 < n` hypothesis mirrors §3.4's "for `n > 0` attributes".

This probability-one form is strictly stronger than a negligible-error
statement. The concrete schemes meet it by sampling issuance randomness
from punctured domains (the `Construction.lean` convention of the μCMZ
base MAC, e.g. `U ←$ G×`), which conditions the paper's literal `ℤ_p`
samplers away from their zero cases; each instance records that
distribution delta. A scheme with genuine correctness error would need a
probabilistic restatement.
-/
def Correct (tok : ATSyntax ProbComp) : Prop :=
  ∀ (secParam n : Nat), 0 < n →
  ∀ (crs : tok.Crs secParam n), crs ∈ support (tok.setup secParam n) →
  ∀ (keys : tok.Sk crs × tok.Pp crs), keys ∈ support (tok.keygen crs) →
  ∀ (m : tok.MsgVec crs),
    ∀ σ? ∈ support (tok.issue crs keys.1 keys.2 m),
      ∃ σ, σ? = some σ ∧ tok.verify crs keys.1 m σ = true

end ATSyntax

end KVAC.Preliminaries
