/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Preliminaries.Assumptions
import KVAC.Preliminaries.AnonymousTokens
import KVAC.Preliminaries.AnonymousTokens.Security

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

DL, q-DL (with the 3-DL instance Theorem 5.1 quotes and the 2-DL
instance Theorem 5.3 quotes), and gap-DL with its DDH oracle are merged
as `OracleComp`-based advantage bounds.

*TODO (Track Pre).* q-DDHI is needed only by the §8.2 rate-limiting
extension (the HashDY PRF of Theorem 8.7) and is deferred with it; DDH
is consumed from VCV-io upstream when a track first needs it.

:::definition "hardness_assumptions" (lean := "KVAC.Preliminaries.dlogAdv, KVAC.Preliminaries.QDLogAdversary, KVAC.Preliminaries.qdlogExp, KVAC.Preliminaries.qdlogAdv, KVAC.Preliminaries.twoDlogAdv, KVAC.Preliminaries.threeDlogAdv, KVAC.Preliminaries.GapDLogAdversary, KVAC.Preliminaries.GapDLogOracleSpec, KVAC.Preliminaries.gapDdhOracleImpl, KVAC.Preliminaries.gapDlogExp, KVAC.Preliminaries.gapDlogAdv") (parent := "pre_assumptions") (tags := "paper, O24 §3.1")
*O24 Section 3.1.* The hardness assumptions over a prime-order group
generator used throughout: discrete log and its gap variant, the q-DL
family (with its 2-DL and 3-DL instances), and q-DDHI. Merged in full
except q-DDHI,
which O24 needs only for the §8.2 rate-limiting extension's HashDY PRF
and is deferred with that extension; DDH itself is consumed from VCV-io
upstream.
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
scheme directories (Track CMZ-OMUF states Theorem 5.11 over this game).

:::definition "anonymous_tokens" (lean := "KVAC.Preliminaries.ATSyntax, KVAC.Preliminaries.ATSyntax.issue, KVAC.Preliminaries.ATSyntax.Correct, KVAC.Preliminaries.AnonymousToken") (parent := "pre_anontoken") (tags := "paper, O24 §3.4")
*O24 Section 3.4.* Syntax and correctness of anonymous token schemes
with non-interactive issuance: a "blind MAC" `AT = (S, K, I, V)`. The
setup half is inherited from {uses "keyed_setup"}[]; this layer adds the
one-round blind issuance split into its moves (`issueUsr₁`, `issueSrv`,
`issueUsr₂`, with both the server's rejection and the user's abort
carried by `Option` — the server of `μBBS_AT` keeps its `C′ ≠ 0` check
even without the issuance proof) and the deterministic keyed verification
`V`. The derived `issue` chains the moves, `Correct` states
support-based (probability-one) correctness with the `0 < n` domain of
Section 3.4, and `AnonymousToken` bundles syntax with correctness at the
paper level. Section 3.4 also demands *unlinkability* but omits its
formal definition (deferring to the literature, with keyed-verification
token systems satisfying the stronger §4 anonymity instead); it is
accordingly not formalized here.
:::

:::definition "omuf_game" (lean := "KVAC.Preliminaries.OMUFQuery, KVAC.Preliminaries.OMUFOracleSpec, KVAC.Preliminaries.OMUFAdversary, KVAC.Preliminaries.SignLog, KVAC.Preliminaries.omufOracleImpl, KVAC.Preliminaries.OMUFWins, KVAC.Preliminaries.OMUFGame, KVAC.Preliminaries.OMUFAdv") (parent := "pre_anontoken") (tags := "paper, O24 Fig 6")
*O24 Figure 6.* The one-more unforgeability game for an anonymous token
scheme {uses "anonymous_tokens"}[] with non-interactive issuance: after `q`
blind-issuance sessions the adversary must present `q + 1` valid
pairwise-distinct message/token pairs. Mirrors the UF-CMVA game
{bpref "ufcmva_game"}[]: a Sign/Verify query menu, a logged
honest oracle implementation (the log's length is Figure 6's dynamic
counter `q`), the experiment as a `ProbComp Bool` with the three-clause
win condition `OMUFWins`, and the advantage `OMUFAdv`. Static
query-budget hypotheses belong to the security theorems over this game,
not to the game itself.
:::
