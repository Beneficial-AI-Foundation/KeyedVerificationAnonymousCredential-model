/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Preliminaries.AnonymousTokens.Construction
import VCVio.CryptoFoundations.SecExp

/-!
# One-more unforgeability for an anonymous token (O24 Figure 6)

The one-more unforgeability (OMUF) game for an `ATSyntax ProbComp`,
following O24 §3.4 and Figure 6, and mirroring the UF-CMVA layer
(`KVAC.Core.AlgebraicMAC.Security`) construct for construct, except that the
adversary also has a private coin oracle and the experiment is generic in the
carrier. After `q` blind-issuance sessions, the adversary must present `q + 1`
valid message/token pairs with pairwise-distinct messages.

## Layout

- `OMUFQuery` — an inductive type enumerating the two oracles.
- `OMUFOracleSpec` — the `OracleSpec` parametrised by `OMUFQuery`.
- `OMUFAdversary` — adversaries: `OracleComp`-valued programs that take
  `(crs, pp)` and return candidate message/token pairs.
- `SignLog` — list of issuance requests answered during the game; its
  length is Figure 6's query counter `q`.
- `omufOracleImpl` — `QueryImpl` that honestly implements Sign and Verify
  for a fixed secret key, threading the `SignLog` via `StateT`.
- `OMUFWins` — the Figure 6 winning condition, as a reusable decidable
  proposition.
- `omufExp` — the experiment over any carrier `OracleComp spec`.
- `OMUFGame` — `omufExp` at `ProbComp`.
- `OMUFAdv` — the OMUF advantage `Pr[= true | OMUFGame]`.

## Design notes

**Query count `q` is dynamic.** Figure 6 reads `q` off the run (`q := q + 1`
in the Sign oracle); here `q` is the length of the `SignLog` at the end of
the game, so the win condition `q + 1` moves with the adversary's behaviour.
Security *theorems* over this game (Track CMZ-OMUF, Theorem 5.11) are
expected to add a static query-budget hypothesis so their `q`-dependent
bounds are well-formed; the game itself, like the merged UF-CMVA and AGM
games, carries none.

**Every Sign query counts.** The Sign oracle logs the request whether or
not the server rejects it — Figure 6 increments `q` before the response.

**The adversary has a private coin oracle.** Its oracle specification is
`unifSpec + OMUFOracleSpec tok crs`, and `OMUFGame` answers that oracle in
`ProbComp`. The comparison with fixed coins is in `DESIGN_ALTERNATIVES.md`,
*One-more forgers have a private coin oracle*.

**Generic in the carrier.** `OMUFQuery`, `OMUFOracleSpec`, `SignLog`,
`omufOracleImpl` and `OMUFWins` take a scheme over any monad `M`, and the
experiment `omufExp` runs over any carrier `OracleComp spec`; `OMUFAdversary`,
`OMUFGame` and `OMUFAdv` are at `ProbComp`. The design is in
`DESIGN_ALTERNATIVES.md`, *Two carriers for one-more unforgeability*.
-/

namespace KVAC.Preliminaries

open OracleSpec OracleComp ENNReal

variable {secParam n : Nat}
variable {M : Type → Type} [Monad M]

/--
The two oracles an OMUF adversary can query against an anonymous-token
scheme for a fixed `crs`:

- `sign µ` — submit an issuance request `µ` to the server (Figure 6's
  `Sign`, which runs `AT.I.Srv(sk, µ)` and advances the query count);
- `verify m σ` — ask whether `σ` is a valid token for `m` (Figure 6's
  `Verify`).

Mirrors `KVAC.Core.UFQuery`. Note the Sign oracle takes the *user message*
`µ`, not an attribute vector: the adversary blinds for itself, which is
what makes the issuance blind.
-/
inductive OMUFQuery (tok : ATSyntax M)
    (crs : tok.Crs secParam n) : Type where
  /-- Submit an issuance request `µ` to the server. -/
  | sign : tok.IssueMsg crs → OMUFQuery tok crs
  /-- Ask whether `σ` is a valid token for `m`. -/
  | verify : tok.MsgVec crs → tok.Token crs → OMUFQuery tok crs

/--
The `OracleSpec` for OMUF: each `OMUFQuery` oracle maps to the response type
the adversary expects.

- `sign µ` ↦ `Option (tok.BlindToken crs)` (`none` = the server rejected)
- `verify m σ` ↦ `Bool`
-/
def OMUFOracleSpec (tok : ATSyntax M)
    (crs : tok.Crs secParam n) : OracleSpec (OMUFQuery tok crs)
  | .sign _ => Option (tok.BlindToken crs)
  | .verify _ _ => Bool

/--
An OMUF adversary: a program that, given the CRS and the public
parameters, queries a private coin oracle and the Sign / Verify oracles,
then outputs a list of candidate message/token pairs — Figure 6's
`(m⃗ᵢ, σᵢ)_{i=1}^{q+1}`.
Figure 6 writes `A^{Sign,Verify}(pp)` and infers the crs from `pp`. The
crs is passed alongside `pp` here, matching `UFAdversary`, since it is
public. The list's required length `q + 1` depends on the run (`q` =
number of Sign queries made), so the type is a bare list and the game
checks the length.
-/
structure OMUFAdversary (tok : ATSyntax ProbComp) where
  /-- The adversary's program: from `(crs, pp)`, query Sign / Verify and
  output the candidate message/token pairs. -/
  run : {secParam n : Nat} → (crs : tok.Crs secParam n) → tok.Pp crs →
    OracleComp (unifSpec + OMUFOracleSpec tok crs)
      (List (tok.MsgVec crs × tok.Token crs))

/--
The list of issuance requests the server has answered so far during an
OMUF experiment. Threaded as `StateT` state through `omufOracleImpl`; its
*length* is Figure 6's query counter `q`, read off at the end of the game.
-/
abbrev SignLog (tok : ATSyntax M)
    (crs : tok.Crs secParam n) : Type :=
  List (tok.IssueMsg crs)

/--
Honest implementation of the OMUF oracles for a fixed secret key `sk`.
The Sign branch runs `tok.issueSrv` and prepends the request to the log —
Figure 6's `q := q + 1`, which fires on *every* Sign query, rejected or
not; the Verify branch runs `tok.verify` and leaves the log unchanged.
-/
def omufOracleImpl (tok : ATSyntax M)
    (crs : tok.Crs secParam n) (sk : tok.Sk crs) :
    QueryImpl (OMUFOracleSpec tok crs) (StateT (SignLog tok crs) M)
  | .sign μ => StateT.mk fun signed =>
      tok.issueSrv crs sk μ >>= fun resp? => pure (resp?, μ :: signed)
  | .verify m σ => StateT.mk fun signed =>
      pure (tok.verify crs sk m σ, signed)

/--
The Figure 6 winning condition, for `q` Sign queries and output list
`out`: exactly `q + 1` entries, pairwise-distinct message vectors
(`List.Nodup`, Figure 6's `∀ i ≠ j : m⃗ᵢ ≠ m⃗ⱼ`), and every pair verifying
(`∀ i ∈ [q+1] : AT.V(sk, m⃗ᵢ, σᵢ) = 1`). A named `Prop` (decidable, so the
game can `decide` it) so that the security theorems and the
AGM OMUF game (Track CMZ-OMUF) can reuse it verbatim.
-/
abbrev OMUFWins (tok : ATSyntax M) (crs : tok.Crs secParam n)
    (sk : tok.Sk crs) (q : Nat)
    (out : List (tok.MsgVec crs × tok.Token crs)) : Prop :=
  out.length = q + 1 ∧ (out.map Prod.fst).Nodup ∧
    ∀ p ∈ out, tok.verify crs sk p.1 p.2 = true

/--
The Figure 6 experiment over a carrier `OracleComp spec`: setup and key
generation, then `run` with its `spec` queries forwarded to the carrier and its
Sign / Verify queries answered by `omufOracleImpl`; `true` iff `OMUFWins` holds
with `q` the number of Sign queries made.
-/
def omufExp {ι : Type} {spec : OracleSpec ι} (tok : ATSyntax (OracleComp spec))
    (secParam n : Nat)
    (run : (crs : tok.Crs secParam n) → tok.Pp crs →
      OracleComp (spec + OMUFOracleSpec tok crs) (List (tok.MsgVec crs × tok.Token crs))) :
    OracleComp spec Bool := do
  let crs ← tok.setup secParam n
  let (sk, pp) ← tok.keygen crs
  let impl := (QueryImpl.ofLift spec (OracleComp spec)).liftTarget
    (StateT (SignLog tok crs) (OracleComp spec)) + omufOracleImpl tok crs sk
  let (out, signed) ← (simulateQ impl (run crs pp)).run []
  pure (decide (OMUFWins tok crs sk signed.length out))

/--
The one-more unforgeability experiment (O24 Figure 6) as a `ProbComp Bool`:
`omufExp` with the adversary's private coin oracle answered by `ProbComp`. The
game is stated for every `n`; §3.4's `n > 0` domain enters through
`ATSyntax.Correct` and the security theorems.
-/
def OMUFGame (tok : ATSyntax ProbComp) (A : OMUFAdversary tok)
    (secParam n : Nat) : ProbComp Bool :=
  omufExp tok secParam n A.run

/--
The OMUF advantage of an adversary `A` against `tok` at parameters
`secParam` and `n`: the probability that `OMUFGame` returns `true` —
O24 §3.4's `Adv^omuf_{AT,A}(λ)`.

A scheme is one-more unforgeable if this advantage is negligible in
`secParam` for every PPT adversary; the asymptotic / negligibility
statement, and the static query-budget hypotheses the concrete bounds
need, live with the security theorems (Track CMZ-OMUF,
Theorem 5.11).
-/
noncomputable abbrev OMUFAdv (tok : ATSyntax ProbComp)
    (A : OMUFAdversary tok) (secParam n : Nat) : ℝ≥0∞ :=
  Pr[= true | OMUFGame tok A secParam n]

end KVAC.Preliminaries
