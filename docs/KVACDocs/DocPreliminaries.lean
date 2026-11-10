/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Preliminaries.Assumptions
import KVAC.Preliminaries.CoinTape
import KVAC.Complexity.Prog
import KVAC.Preliminaries.AnonymousTokens
import KVAC.Preliminaries.AnonymousTokens.Security
import KVAC.Preliminaries.AnonymousTokens.OracleCarrier

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

:::theorem "coin_tape_not_uniform" (lean := "KVAC.Preliminaries.not_forall_card_fiber_mul_eq, KVAC.Preliminaries.map_uniform_bits_ne_uniform") (parent := "pre_assumptions") (tags := "milestone")
A finite tape of coin bits gives no exact draw from `ℤ_p`. O24 Section 3
(p. 24) writes the length of the random coins of a p.p.t. algorithm as
`A.rl(λ)`, and the extractability clause of Definition 7.1 (p. 58) samples the
coins as bits. Figure 9 (p. 34) draws `s ←$ ℤ_p`. For an odd prime `p` and any
function `f` of `k` coin bits, the image of the uniform distribution on the
tapes under `f` is not the uniform distribution on `ZMod p`
(`map_uniform_bits_ne_uniform`). The function `f` is an algorithm with its
inputs and its oracle answers fixed, with no bound on its running time. The
finding is in Part A6.6 of `docs/findings/FINDINGS_AND_LESSONS.md`.
:::

:::proof "coin_tape_not_uniform"
Each tape has probability `2 ^ (-k)`, so a value `y` has probability
`m / 2 ^ k`, where `m` counts the tapes that `f` sends to `y`. Uniformity gives
`m * p = 2 ^ k` (`not_forall_card_fiber_mul_eq`). Then `p` divides `2 ^ k`,
hence `2`, which no odd prime does.
:::

# P.p.t. algorithms as programs

:::group "pre_ppt"
P.p.t. algorithms as programs
:::

O24 states its security properties for p.p.t. adversaries. An `OracleComp`
computation has no running time, so the repository had no predicate for the
class (issue #240). The file `KVAC/Complexity/Prog.lean` defines a language
whose terms are programs, with a running time polynomial computed from the
syntax.

:::definition "prog_language" (lean := "KVAC.Complexity.Ty, KVAC.Complexity.instDecidableEqTy, KVAC.Complexity.Ty.interp, KVAC.Complexity.Ctx, KVAC.Complexity.Var, KVAC.Complexity.Env, KVAC.Complexity.Env.get, KVAC.Complexity.Sig, KVAC.Complexity.Sig.spec, KVAC.Complexity.Expr, KVAC.Complexity.Expr.size, KVAC.Complexity.Expr.eval, KVAC.Complexity.Prog") (parent := "pre_ppt") (tags := "milestone")
The language of programs. The sorts `Ty` are abstract, so a term mentions no
field and no group, and one term runs at the group of every security
parameter. Variables are de Bruijn indices, so a continuation is a term and
not a Lean function. An expression `Expr` is pure. A program `Prog` returns an
expression, binds a program, queries an oracle of its signature `Sig`, draws a
fair coin, draws an exactly uniform scalar, branches, or iterates a body a
number of times that is a polynomial in the security parameter. A group value
arises only as a variable, as an oracle answer, as zero or as the result of a
group operation. The exact draw follows Figure 9 (p. 34), and
{bpref "coin_tape_not_uniform"}[] is the reason why a fair coin alone does not
give it.
:::

:::definition "prog_cost" (lean := "KVAC.Complexity.Prog.timePoly, KVAC.Complexity.Prog.coinPoly, KVAC.Complexity.Prog.CoinOnly") (parent := "pre_ppt") (tags := "milestone")
The resource bounds of a program of {uses "prog_language"}[], computed from
the syntax. The running time polynomial `timePoly` charges one unit per field
operation, group operation, query and draw, and a loop multiplies the bound of
its body by its iteration polynomial. The polynomial `coinPoly` bounds the fair
coins. The predicate `CoinOnly` holds for a program with no exact draw, the
programs whose randomness is the coin tape of O24 Section 3 (p. 24).
:::

:::definition "prog_interp" (lean := "KVAC.Complexity.iterM, KVAC.Complexity.Prog.interp") (parent := "pre_ppt") (tags := "milestone")
The interpretation of a program of {uses "prog_language"}[] at a security
parameter, a field and a group. It is an `OracleComp` computation over
`unifSpec + S.spec F G`, the carrier of the adversaries of the repository, so
the games and the concrete inequalities apply to it unchanged.
:::

:::theorem "prog_query_bound" (lean := "KVAC.Complexity.IsOracleQuery, KVAC.Complexity.instDecidablePredSumNatSigmaInterpDomIsOracleQuery, KVAC.Complexity.isQueryBoundP_liftComp_probComp, KVAC.Complexity.isQueryBoundP_iterM, KVAC.Complexity.Prog.isQueryBoundP_interp") (parent := "pre_ppt") (tags := "milestone")
The interpretation of {uses "prog_interp"}[] at the security parameter `λ`
makes at most `timePoly.eval λ` queries to the oracles of its signature, for
the polynomial of {uses "prog_cost"}[]. The number of queries of a program
is therefore bounded by a polynomial in `λ`.
:::

:::proof "prog_query_bound"
By induction on the program. A coin and an exact draw query the coin oracle
alone (`isQueryBoundP_liftComp_probComp`). A bind adds the bounds of its two
parts. A branch runs one arm, and the polynomial counts both. A loop of `k`
steps makes at most `k` times the queries of its body
(`isQueryBoundP_iterM`).
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
scheme directories (the `μCMZ_AT` analysis states Theorem 5.11 over the
AGM form of this game).

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

:::definition "omuf_game" (lean := "KVAC.Preliminaries.OMUFQuery, KVAC.Preliminaries.OMUFOracleSpec, KVAC.Preliminaries.OMUFAdversary, KVAC.Preliminaries.SignLog, KVAC.Preliminaries.omufOracleImpl, KVAC.Preliminaries.OMUFWins, KVAC.Preliminaries.omufExp, KVAC.Preliminaries.OMUFGame, KVAC.Preliminaries.OMUFAdv") (parent := "pre_anontoken") (tags := "paper, O24 Fig 6")
*O24 Figure 6.* The one-more unforgeability game for an anonymous token
scheme {uses "anonymous_tokens"}[] with non-interactive issuance: after `q`
blind-issuance sessions the adversary must present `q + 1` valid
message/token pairs with pairwise-distinct messages. Mirrors the UF-CMVA game
{bpref "ufcmva_game"}[]: a Sign/Verify query menu, a logged
honest oracle implementation (the log's length is Figure 6's dynamic
counter `q`), the experiment `omufExp` with the three-clause win condition
`OMUFWins`, the game `OMUFGame` at `ProbComp`, and the advantage `OMUFAdv`.
Unlike the UF-CMVA game, the experiment runs over any carrier `OracleComp spec`,
and the adversary also has a private coin oracle, as VCV-io's PRF, IND-CPA and
Fischlin adversaries do. Static query-budget hypotheses belong to the security
theorems over this game, not to the game itself.
:::

:::definition "omuf_game_ro" (lean := "KVAC.Preliminaries.OMUFAdversaryRO, KVAC.Preliminaries.OMUFGameRO, KVAC.Preliminaries.OMUFAdvRO") (parent := "pre_anontoken") (tags := "milestone")
The one-more unforgeability game of {uses "omuf_game"}[] at the oracle carrier
`OracleComp (ZKRO H)` of {uses "zk_game"}[], for a scheme whose algorithms
query the random oracle, such as one whose server attaches a Fiat–Shamir
proof. The adversary queries the same oracle beside Sign and Verify, and the
experiment runs through one random-oracle cache from empty, so the server's
proofs and the adversary's hash queries share it. The experiment is that of
the plain game, generic in the carrier.
:::

:::definition "at_correctness_ro" (lean := "KVAC.Preliminaries.ATSyntax.CorrectRO") (parent := "pre_anontoken") (tags := "milestone")
Correctness of {uses "anonymous_tokens"}[] at the oracle carrier
`OracleComp (ZKRO H)` of {uses "zk_game"}[]: setup, key generation and
issuance thread one random-oracle cache, so that a scheme's Fiat–Shamir proofs
share the oracle.
:::

:::theorem "omuf_ro_bridge" (lean := "KVAC.Preliminaries.ATSyntax.lift, KVAC.Preliminaries.omufLiftImpl, KVAC.Preliminaries.OMUFAdversary.lift, KVAC.Preliminaries.omufAdvRO_lift") (parent := "pre_anontoken") (tags := "milestone")
The bridge between the two carriers. A scheme over `ProbComp` lifts to the
oracle carrier with its algorithms behind `liftM`, and an adversary of the
plain game {uses "omuf_game"}[] lifts with its queries translated. The lifted
pair has, in the game at the oracle carrier {uses "omuf_game_ro"}[], the
advantage the original pair has in the plain game.
:::

:::proof "omuf_ro_bridge"
Neither the lifted scheme nor the lifted adversary queries `H`. The lifted
experiment is the plain one embedded by `liftM`: the scheme's algorithms are
`liftM`s by definition, and the adversary's run follows by induction over its
simulation, each translated query answered as the plain game answers it. By
{uses "runro_lift"}[], running the embedded experiment from the empty cache
leaves the cache empty and gives the plain experiment's outputs.
:::
