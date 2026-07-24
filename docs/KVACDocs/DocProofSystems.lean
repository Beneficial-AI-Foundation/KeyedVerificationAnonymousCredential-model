/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal


#doc (Manual) "Proof systems" =>
%%%
tag := "proof_systems"
%%%

The proof-system technology that underpins every credential proof,
corresponding to O24 Section 9 plus supporting Σ-protocol meta-theory.
Three files under `KVAC/ProofSystems/`:

- `SigmaProtocol.lean` — Σ-protocol theory,
- `FiatShamir.lean` — the non-interactive transformation in the random-oracle model,
- `StraightLineExtraction.lean` — straight-line extraction in the algebraic group model.

The paper's security proofs in Sections 5 and 6 lean heavily on
straight-line extraction; investing in proven meta-theory here pays off
across every later track.

# Σ-protocol theory

:::group "ps_sigma"
The classical three-move Σ-protocol API: prover commits, verifier
challenges, prover responds, verifier accepts or rejects. The three core
properties are completeness, special soundness, and honest-verifier
zero-knowledge.
:::

The three μCMZ instances are merged on VCV-io's upstream
`SigmaProtocol` structure — completeness, honest-verifier
zero-knowledge, and special soundness for `R_iu`, `R_is`, and `R_p` (see
{bpref "mucmz_sigma_protocols"}[] in the *μCMZ* chapter). No
project-local Σ-protocol typeclass proved necessary.

*TODO (Track Σ).* Provide combinators for AND / OR /
equality-of-discrete-log compositions as needed by the schemes'
presentation proofs.

# Fiat–Shamir transformation

:::group "ps_fs"
The Fiat–Shamir transformation makes a Σ-protocol non-interactive by
deriving the verifier's challenge from a hash of the transcript. In the
random-oracle model, the resulting NIZK inherits knowledge soundness
from the underlying Σ-protocol's special soundness.
:::

*TODO (Track Σ).* State the Fiat–Shamir transformation and prove the
standard inheritance lemmas: completeness, knowledge soundness in the
ROM, zero-knowledge.

# Straight-line extraction

:::group "ps_sle"
Straight-line extraction in the algebraic group model — the technique
that makes both schemes' extractability proofs go through without
rewinding. Required by Theorem 5.2 (μCMZ extractability) and the
analogous μBBS theorem; the meta-theorem proved once here makes every
credential-proof instance a one-line application.
:::

*TODO (Track Σ).* Formalise straight-line extraction in the AGM,
mirroring Section 9. State the meta-theorem the two schemes'
extractability chapters quote.
