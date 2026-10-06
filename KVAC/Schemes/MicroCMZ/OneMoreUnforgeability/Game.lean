/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import KVAC.Schemes.MicroCMZ.ATVariant
import KVAC.Preliminaries.AnonymousTokens.Security

/-!
# μCMZ_AT one-more unforgeability: the AGM-instrumented game (O24 §5.6)

The algebraic group model (AGM) one-more unforgeability game for the μCMZ_AT
core scheme (`μCMZATCoreSyntax`), following Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §5.6, and closely mirroring the
AGM UF-CMVA(+Help) scaffolding of `KVAC.Schemes.MicroCMZ.AlgebraicMAC`. This is
step A4 of #12 (Track CMZ-OMUF, issue #181), delivered in two parts: first the
representation gate, the query type, the oracle spec, the transcript log, and
the instrumented oracles; then the algebraic adversary, the winning condition,
the experiment `AGM_OMUFGame`, and its advantage `AGM_OMUFAdv`, together with
the decidable Sign predicate the static query-budget hypotheses of Theorem 5.11
count.

A word of caution on naming, as in the MAC module: this is scaffolding, not the
honest Figure 6 game. The oracles are *gated*. They answer honestly only when
the submitted representation is consistent, and refuse otherwise, so the game
matches the plain `OMUFGame` of `KVAC.Preliminaries.AnonymousTokens.Security`
only for adversaries that always submit consistent, exact-length
representations. A theorem about this game is not by itself a theorem about
the plain game; that correspondence is the OMUF analogue of the MAC track's
`WellBehaved` bridge (#81) and is deferred to Phase B of the Theorem 5.3 plan.

## Where the representations sit

In the plain Figure 6 game the adversary hands the Sign oracle a bare commitment
`C'` and receives the blinded pair `(U', V')`. In the algebraic group model every
group element the adversary *submits* carries an algebraic representation over
the basis it has seen so far: the fixed elements `G₀, H, X₀, Xᵣ, X⃗` and one
`(αᵤ, αᵥ)` pair per blinded pair issued (O24 Equation 17 for the commitments,
Equation 19 for the forgeries). The representation type is the MAC game's
`AGMRepr`, unchanged: the core shares setup and key generation with the base
MAC, so the fixed basis is the same, and the Sign answers are pairs of group
elements like the MAC tags, so they extend the basis the same way.

The MAC oracle gates the group-element *arguments* of its Verify and Help arms,
while its Sign arm takes a message and no group element. Here Sign takes a group
element, the commitment, so it is the first arm in the repository to gate an
issuance request on the way in. That is what the Theorem 5.11 proof needs, since
Equation 18 substitutes each commitment's representation into the server's
answer.

## Design notes (Track CMZ-OMUF decisions, September 2026)

**Gate on the way in.** The Sign oracle evaluates the submitted representation
over the current public elements and issued pairs and compares it with the
submitted commitment. On a match it answers through the core's server
algorithm, on a mismatch it refuses with `none`. Gating the answers rather than
restricting the adversary type is the merged MAC game's choice. The gate is
computable from the adversary's own view, so a refusal reveals nothing about
the secret key, an adversary loses nothing by pre-checking its own queries, and
the stricter conventions below cannot strengthen it.

**Exact-length tag coefficients.** The representation's tag-coefficient list
must have exactly one entry per blinded pair issued so far, else the query is
refused. This departs from `AGMRepr.eval`'s permissive `zipWith`, which ignores
excess entries and reads missing ones as zero. The rule is a simplification, not
a soundness requirement. It buys one guarantee: `AGMRepr.eval` of an accepted
representation is unchanged under any later extension of the transcript, so the
winning condition and the reduction can read the finished log against one final
list of pairs instead of carrying a per-query prefix. `reprMatches` itself is
not stable, since its length conjunct fails once more pairs exist, so lemmas
about an earlier commitment must evaluate its representation, never re-check the
gate, at a grown transcript (`AGMRepr.eval_append_of_length_eq`,
`reprMatches_eval_append`). The comparison with the permissive and the
canonical-form alternatives is in `DESIGN_ALTERNATIVES.md`, *Exact-length
representations in the AGM OMUF game*.

**The log keeps the representations.** Every Sign query is logged in issuance
order as the commitment, its representation, and the server's answer, `none`
when the gate refused. The winning condition reads only the log's length and
its issued pairs, but the Theorem 5.11 reduction substitutes each accepted
commitment's representation into the polynomial of its answer (Equation 18),
and group elements do not determine the representation the adversary chose, so
the game transcript retains it rather than leaving it to a separate reduction
trace.

**Every Sign query counts, issued or refused.** Figure 6 increments its counter
`q` before calling the server (`q := q + 1`, then `return AT.I.Srv(sk, µ)`), and a
refused query must not be a free probe, so the counter the winning condition
reads is the log length. The representation basis, by contrast, is the list of
pairs actually issued, read off the log by `AGMOMUFLog.tags`
(`AGMOMUFLog.tags_length_le`). Two lengths, one for the budget and one for the
basis. After a refusal, the issuance index and the Sign-query index differ, and
the polynomial bookkeeping of the proof indexes by issuance.

**Dynamic count here, static budget in the theorems.** As in the plain game and
the MAC games, the oracle carries no query bound. The Theorem 5.11 statements add
a static hypothesis on the adversary (`IsQueryBoundP` over the Sign arm, at most
`q` queries) so that their `q`-dependent bounds are well-formed.

**Carrier.** `ProbComp`, as for the core scheme and the MAC games. The core never
calls a hash, so no random oracle is threaded. The `π_is`-carrying variant of
item 18 lives over `OracleComp (ZKRO H)` and gets its own game.

**Order of the log.** The plain game prepends requests (`μ :: signed`), which is
harmless there because only the length is read. Here the pairs extend the
representation basis in issuance order, so the log appends, as `AGMLog` does.

**What carries over from the MAC track.** The representation type and the
coefficient conversion `AGMRepr.toReprCoeffs` apply to exact-length lists as
they are. The MAC track's evaluation bridge `agmRepr_eval_eq_eval_toPoly` does
not, since a blind-issuance answer `V' = (x₀ + xᵣ)·U' + u·C'` is not a MAC tag
on a known message. The Equation 18 bridge is new work for the Theorem 5.11
proof.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

/-! ## Queries, responses and the log

These need only the bare types `F`, `G` and `n`, so they sit outside the
typeclass block below and carry no algebraic hypotheses. -/

section Data

variable {F G : Type} {n : ℕ}

/--
The two oracle arms of the AGM one-more unforgeability game for μCMZ_AT (O24
Figure 6, instrumented per §5.6).
-/
inductive AGMOMUFQuery (F G : Type) (n : ℕ) : Type where
  /-- `sign C' ρ` — an issuance request: the Pedersen commitment `C'` (Figure 9's
  user message, the core sends no `π_iu`) with its representation over the
  transcript so far (O24 Equation 17). Gated on the way in. -/
  | sign : G → AGMRepr F n → AGMOMUFQuery F G n
  /-- `verify m⃗ (U, V) ρ_U ρ_V` — a verification query for the token `(U, V)` on
  the attributes `m⃗`, each component with a representation, gated like the MAC
  game's `verify` arm and with the same exact-length rule as `sign`. -/
  | verify : (Fin n → F) → Code G → AGMRepr F n → AGMRepr F n → AGMOMUFQuery F G n

/--
Response types for `AGMOMUFQuery`: the server's blinded pair `(U', V')` for
`sign`, as an `Option` (`none` when the gate refuses, mirroring the plain game's
`none` for a rejecting server); a Boolean for `verify`.
-/
def AGMOMUFOracleSpec (F G : Type) (n : ℕ) : OracleSpec (AGMOMUFQuery F G n)
  | .sign _ _ => Option (G × G)
  | .verify _ _ _ _ => Bool

/--
The transcript log threaded through the game: every Sign query in issuance
order, each as the submitted commitment, its representation, and the server's
answer, `none` when the gate refused it. The log's *length* is Figure 6's query
counter `q` (every Sign query counts); its issued pairs, `AGMOMUFLog.tags`,
extend the representation basis; the representations are kept for the
Theorem 5.11 reduction (see *The log keeps the representations* in the module
docstring).
-/
abbrev AGMOMUFLog (F G : Type) (n : ℕ) : Type := List (G × AGMRepr F n × Option (G × G))

/-- The blinded pairs actually issued so far, in issuance order: the tag part of
the representation basis. Refused queries contribute nothing. -/
def AGMOMUFLog.tags (log : AGMOMUFLog F G n) : List (G × G) :=
  log.filterMap fun e => e.2.2

/-- The empty transcript has issued nothing. -/
@[simp] theorem AGMOMUFLog.tags_nil : AGMOMUFLog.tags ([] : AGMOMUFLog F G n) = [] := rfl

/-- Appending an issued query extends the basis by its pair. -/
@[simp] theorem AGMOMUFLog.tags_append_some (log : AGMOMUFLog F G n) (C' : G)
    (ρ : AGMRepr F n) (p : G × G) :
    AGMOMUFLog.tags (log ++ [(C', ρ, some p)]) = AGMOMUFLog.tags log ++ [p] := by
  simp [AGMOMUFLog.tags]

/-- Appending a refused query leaves the basis unchanged. -/
@[simp] theorem AGMOMUFLog.tags_append_none (log : AGMOMUFLog F G n) (C' : G)
    (ρ : AGMRepr F n) :
    AGMOMUFLog.tags (log ++ [(C', ρ, none)]) = AGMOMUFLog.tags log := by
  simp [AGMOMUFLog.tags]

/-- Issued pairs never outnumber Sign queries: the basis length is at most the
budget length, the arithmetic behind the pigeonhole step of Theorem 5.11. -/
theorem AGMOMUFLog.tags_length_le (log : AGMOMUFLog F G n) :
    (AGMOMUFLog.tags log).length ≤ log.length :=
  List.length_filterMap_le _ _

/--
The Sign arm as a predicate on queries: the one the static query-budget
hypotheses of the Theorem 5.11 statements count, as
`IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q` (at most `q` Sign queries,
Verify queries free). Refused Sign queries are Sign queries.
-/
def AGMOMUFQuery.isSign : AGMOMUFQuery F G n → Prop
  | .sign _ _ => True
  | .verify _ _ _ _ => False

/-- `IsQueryBoundP` needs the predicate decidable. -/
instance AGMOMUFQuery.instDecidablePredIsSign :
    DecidablePred (AGMOMUFQuery.isSign (F := F) (G := G) (n := n))
  | .sign _ _ => isTrue trivial
  | .verify _ _ _ _ => isFalse id

/--
One forgery of the algebraic adversary (O24 Equation 19): the attribute vector
`m⃗`, the token `(U, V)`, and one representation per token component over the
final transcript. A structure rather than a tuple, so the winning condition and
the Theorem 5.11 proof read named fields.
-/
structure AGMOMUFForgery (F G : Type) (n : ℕ) where
  /-- The attribute vector `m⃗`. -/
  msg : Fin n → F
  /-- The token `(U, V)`. -/
  token : Code G
  /-- The representation of `U` over the final transcript. -/
  reprU : AGMRepr F n
  /-- The representation of `V` over the final transcript. -/
  reprV : AGMRepr F n

/-- The plain `(m⃗, (U, V))` of a forgery, the part the Figure 6 winning condition
`OMUFWins` reads. -/
def AGMOMUFForgery.plain (e : AGMOMUFForgery F G n) : (Fin n → F) × Code G :=
  (e.msg, e.token)

/--
An algebraic one-more unforgeability adversary against μCMZ_AT for `n`
attributes (O24 §5.6): given the crs `H` and the public parameters
`(X₀, Xᵣ, X⃗)`, it queries the instrumented oracles and outputs its list of
forgeries, `q + 1` of them to win. The shape of `AGMUFAdversary` and the plain
`OMUFAdversary`, with the same inherited limitation: no private coin oracle.
-/
structure AGMOMUFAdversary (F G : Type) (n : ℕ) where
  /-- The adversary's program: from `(H, pp)`, query the instrumented Sign and
  Verify arms and output the forgeries with their representations. -/
  run : G → Params G n →
    OracleComp (AGMOMUFOracleSpec F G n) (List (AGMOMUFForgery F G n))

end Data

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-! ## The representation gate -/

/--
The gate of the AGM OMUF game: a representation `ρ` *matches* a group element
`y` over the fixed basis `(g₀, H, X₀, Xᵣ, X⃗)` and the issued pairs `tags` iff its
tag-coefficient list has exactly one entry per issued pair and it evaluates to
`y` (see *Exact-length tag coefficients* in the module docstring). An `abbrev`,
so decidability is derived and the oracles and the winning condition `decide`
it. The length conjunct is the only difference from the MAC game's consistency
check. It is not stable under extension of `tags`; `AGMRepr.eval` of an
accepted representation is.
-/
abbrev reprMatches (ρ : AGMRepr F n) (g₀ H X₀ Xᵣ : G) (X : Fin n → G)
    (tags : List (G × G)) (y : G) : Prop :=
  ρ.uv.length = tags.length ∧ ρ.eval g₀ H X₀ Xᵣ X tags = y

/--
The exact-length payoff (see *Exact-length tag coefficients* in the module
docstring): a representation with one tag coefficient per pair in `tags`
evaluates identically over any extension `tags ++ suffix`, since `zipWith`
stops at the shorter list. Lemmas about a commitment accepted at an earlier
transcript read its representation through this, never by re-checking the gate.
-/
theorem AGMRepr.eval_append_of_length_eq (ρ : AGMRepr F n) (g₀ H X₀ Xᵣ : G) (X : Fin n → G)
    (tags suffix : List (G × G)) (h : ρ.uv.length = tags.length) :
    ρ.eval g₀ H X₀ Xᵣ X (tags ++ suffix) = ρ.eval g₀ H X₀ Xᵣ X tags := by
  rw [AGMRepr.eval, AGMRepr.eval, ← List.append_nil ρ.uv, List.zipWith_append h,
    List.zipWith_nil_left, List.append_nil, List.append_nil]

/-- An accepted representation keeps naming its element at every later
transcript. -/
theorem reprMatches_eval_append {ρ : AGMRepr F n} {g₀ H X₀ Xᵣ : G} {X : Fin n → G}
    {tags : List (G × G)} {y : G} (hρ : reprMatches ρ g₀ H X₀ Xᵣ X tags y)
    (suffix : List (G × G)) :
    ρ.eval g₀ H X₀ Xᵣ X (tags ++ suffix) = y :=
  (AGMRepr.eval_append_of_length_eq ρ g₀ H X₀ Xᵣ X tags suffix hρ.1).trans hρ.2

/-! ## The instrumented oracle -/

variable (gen : G)

/--
Honest instrumented oracles over the core scheme `μCMZATCoreSyntax F gen` (the
seam this game crosses, as the MAC game crosses `μCMZBaseMACSyntax`), for the
generator `gen` (a section variable, hence the first explicit argument), the
security parameter, the secret key `sk`, the crs `H`, and the public parameters
`pp = (X₀, Xᵣ, X⃗)`. Noncomputable through the core's sampling.

- `sign C' ρ` checks `reprMatches ρ … (tags log) C'`. On a match it runs the
  core's `issueSrv` and appends `(C', ρ, answer)` to the log; on a mismatch it
  refuses, appending `(C', ρ, none)` and answering `none`. Either way the query
  is logged (Figure 6's `q := q + 1`, and a refused query is not a free probe).
- `verify m⃗ σ ρ_U ρ_V` returns the core's `verify` iff both representations
  match their components (else `false`), leaving the log unchanged.
-/
noncomputable def agmOMUFOracleImpl (secParam : ℕ) (sk : Key F n) (H : G)
    (pp : Params G n) :
    QueryImpl (AGMOMUFOracleSpec F G n) (StateT (AGMOMUFLog F G n) ProbComp)
  | .sign C' ρ => StateT.mk fun log =>
      if reprMatches ρ gen H pp.1 pp.2.1 pp.2.2 (AGMOMUFLog.tags log) C' then do
        let resp? : Option (G × G) ←
          (μCMZATCoreSyntax F gen).issueSrv (secParam := secParam) H sk C'
        pure (resp?, log ++ [(C', ρ, resp?)])
      else
        pure (none, log ++ [(C', ρ, none)])
  | .verify m σ ρU ρV => StateT.mk fun log =>
      let tags := AGMOMUFLog.tags log
      let consistent :=
        reprMatches ρU gen H pp.1 pp.2.1 pp.2.2 tags σ.1 ∧
        reprMatches ρV gen H pp.1 pp.2.1 pp.2.2 tags σ.2
      pure (decide consistent &&
        (μCMZATCoreSyntax F gen).verify (secParam := secParam) H sk m σ, log)

/-! ## The winning condition, the experiment and the advantage -/

/--
The winning condition of the AGM OMUF game, read off the final transcript `log`
and the adversary's output `out`: the plain Figure 6 condition `OMUFWins` of
`KVAC.Preliminaries.AnonymousTokens.Security` over the core scheme, with the
query count `q = log.length` (every Sign query counts, refused ones included)
and the forgeries projected to their `(m⃗, (U, V))`, together with
`reprMatches` for both representations of every forgery over the final issued
pairs `AGMOMUFLog.tags log`, so each list has exactly one entry per pair issued
in the whole game. All `q + 1` forgeries are gated alike; the Theorem 5.11 proof
singles out the one not supported by an issued pair by pigeonhole (O24 p. 45).
One inconsistent representation loses the game (it is a gate, not a
hypothesis), which cannot strengthen the adversary since the check is
computable from its own view. An `abbrev`, like `OMUFWins`, so the game can
`decide` it.
-/
abbrev AGMOMUFWins (secParam : ℕ) (sk : Key F n) (H : G) (pp : Params G n)
    (log : AGMOMUFLog F G n) (out : List (AGMOMUFForgery F G n)) : Prop :=
  OMUFWins (μCMZATCoreSyntax F gen) (secParam := secParam) H sk log.length
      (out.map AGMOMUFForgery.plain) ∧
    ∀ e ∈ out,
      reprMatches e.reprU gen H pp.1 pp.2.1 pp.2.2 (AGMOMUFLog.tags log) e.token.1 ∧
      reprMatches e.reprV gen H pp.1 pp.2.1 pp.2.2 (AGMOMUFLog.tags log) e.token.2

/--
The AGM one-more unforgeability experiment for μCMZ_AT (O24 Figure 6,
instrumented per §5.6). Setup and key generation delegate to
`μCMZATCoreSyntax F gen`, as the plain `OMUFGame` delegates to its scheme; the
adversary runs against `agmOMUFOracleImpl` from the empty log; returns `true`
iff `AGMOMUFWins` holds for the final log and the output. Stated for every `n`
and every `secParam` (unused by the core, kept threaded as in the plain game).
The correspondence with the plain `OMUFGame` is the deferred bridge described
in the module docstring.
-/
noncomputable def AGM_OMUFGame (secParam : ℕ) (A : AGMOMUFAdversary F G n) :
    ProbComp Bool := do
  let tok := μCMZATCoreSyntax F gen
  let H : G ← tok.setup secParam n
  let (sk, pp) ← tok.keygen (secParam := secParam) (n := n) H
  let (out, log) ←
    (simulateQ (agmOMUFOracleImpl gen secParam sk H pp) (A.run H pp)).run []
  pure (decide (AGMOMUFWins gen secParam sk H pp log out))

/-- The AGM OMUF advantage `Pr[= true | AGM_OMUFGame …]`, a function of `secParam`
like `AGM_UF_CMVAAdv`. The Theorem 5.11 statements will bound it under a static
`IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q` hypothesis. -/
noncomputable abbrev AGM_OMUFAdv (A : AGMOMUFAdversary F G n) (secParam : ℕ) : ℝ≥0∞ :=
  Pr[= true | AGM_OMUFGame gen secParam A]

end KVAC.Schemes.MicroCMZ
