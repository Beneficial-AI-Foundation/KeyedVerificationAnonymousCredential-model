/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Preliminaries.Assumptions

open Verso.Genre Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true


#doc (Manual) "Preliminaries" =>
%%%
tag := "preliminaries"
%%%

Cryptographic background corresponding to O24, Section 3. Three
independent files under `KVAC/Preliminaries/`:

- hardness assumptions (Section 3.1),
- zero-knowledge argument syntax and properties (Section 3.3),
- anonymous-token syntax and the one-more unforgeability game (Section 3.4).

These statements are shared by every security track; they live here
rather than in each scheme's directory so that μCMZ and μBBS quote
identical hardness lemmas.

# Hardness assumptions

:::group "pre_assumptions"
Hardness assumptions
:::

The cryptographic assumptions used in the formalisation, all bound to
VCV-io's `CryptoFoundations/HardnessAssumptions/` library so that every
security track shares identical statements:

- `DL` (discrete logarithm) — available from VCV-io upstream.
- `DDH` (decisional Diffie–Hellman) — available from VCV-io upstream.
- `q-DL` — introduced project-locally or upstream.
- `q-DDHI` (q-decisional Diffie–Hellman inversion) — introduced project-locally or upstream.
- `gap-DL` — introduced project-locally or upstream.

AGM and GGM are proof-theoretic *adversary models*, not assumptions
about the group; they live in the security-track files where reductions
are stated, not here.

DL, q-DL (with the 2-DL and 3-DL specialisations Theorem 5.1 quotes),
and gap-DL with its DDH oracle are merged as `OracleComp`-based
advantage bounds.

*TODO (Track Pre).* q-DDHI is deferred together with μBBS; DDH is
consumed from VCV-io upstream when a track first needs it.

:::definition "hardness_assumptions" (lean := "KVAC.Preliminaries.dlogAdv, KVAC.Preliminaries.QDLogAdversary, KVAC.Preliminaries.qdlogExp, KVAC.Preliminaries.qdlogAdv, KVAC.Preliminaries.twoDlogAdv, KVAC.Preliminaries.threeDlogAdv, KVAC.Preliminaries.GapDLogAdversary, KVAC.Preliminaries.GapDLogOracleSpec, KVAC.Preliminaries.gapDdhOracleImpl, KVAC.Preliminaries.gapDlogExp, KVAC.Preliminaries.gapDlogAdv") (parent := "pre_assumptions") (tags := "paper, O24 §3.1")
*O24 Section 3.1.* The hardness assumptions over a prime-order group
generator used throughout: discrete log and its gap variant, the
q-strong and 2-power variants, and q-DDHI. Merged in full except q-DDHI,
which O24 needs only for μBBS/HashDY and is deferred with that scheme;
DDH itself is consumed from VCV-io upstream.
:::

# Zero-knowledge arguments

:::group "pre_zkarg"
Zero-knowledge arguments
:::

Abstract NIZK syntax with the three core properties of O24 Section 3.3:
knowledge soundness, zero-knowledge, and simulation-extractability.
Combined with the generic ZK proof typeclass from the *Core* chapter,
this layer states the properties the schemes need to quote when proving
anonymity and extractability.

Syntax, perfect completeness, and the two-world zero-knowledge game are
merged in the *Core* chapter.

*TODO (Track Pre).* Knowledge soundness and simulation extractability
are under review in PR #54.

:::definition "zk_arguments" (parent := "pre_zkarg") (tags := "paper, O24 §3.3")
*O24 Section 3.3.* The zero-knowledge argument interface (prover,
verifier, simulator) with its security notions — completeness,
knowledge soundness, zero-knowledge, and (strong) simulation
extractability — as consumed by the credential presentation proofs.
Syntax and completeness are merged as {uses "nizkp_syntax"}[] and the
zero-knowledge game as {uses "zk_game"}[]; knowledge soundness and
simulation extractability arrive with PR #54.
:::

# Anonymous tokens

:::group "pre_anontoken"
Anonymous tokens
:::

Anonymous-token syntax and the one-more unforgeability (OMUF) game of
O24 Section 3.4. Anonymous tokens are the headline application of the
OMUF notion — used in the `μCMZ_AT` and `μBBS_AT` chapters of the two
scheme directories.

*TODO (Track Pre).* Define the anonymous-token syntax and the OMUF
security game, mirroring Section 3.4.

:::definition "anonymous_tokens" (parent := "pre_anontoken") (tags := "paper, O24 §3.4")
*O24 Section 3.4.* Syntax and security of anonymous token schemes with
non-interactive issuance: a "blind MAC" with setup, key generation, an
issuance protocol, and verification.
:::

:::definition "omuf_game" (parent := "pre_anontoken") (tags := "paper, O24 Fig 6")
*O24 Figure 6.* The one-more unforgeability game for an anonymous token
scheme {uses "anonymous_tokens"}[] with non-interactive issuance: after `q`
blind-issuance sessions the adversary must present `q + 1` valid
pairwise-distinct message/token pairs.
:::
