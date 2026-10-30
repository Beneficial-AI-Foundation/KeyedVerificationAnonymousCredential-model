/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import KVAC.Schemes.MicroCMZ.ATVariant
import KVAC.Preliminaries.AnonymousTokens.Security

/-!
# μCMZ_AT one-more unforgeability: the AGM game (O24 §5.6)

The algebraic group model (AGM) one-more unforgeability game for the μCMZ_AT
core scheme (`μCMZATCoreSyntax`), following Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §5.6, and closely mirroring the
AGM UF-CMVA(+Help) game of `KVAC.Schemes.MicroCMZ.AlgebraicMAC`. This is
step A4 of #12 (Track CMZ-OMUF, issue #181): the query type, the oracle spec,
the transcript log, the oracles, the algebraic adversary, the
winning condition, the experiment `AGM_OMUFGame` and its advantage
`AGM_OMUFAdv`, together with the decidable Sign predicate the static
query-budget hypotheses of Theorem 5.11 count.

The algebraic group model restricts the adversary's type and nothing else.
Every group element the adversary submits, a commitment or a token, is
given by its representation alone, and the oracles and the winning condition
evaluate it and proceed as the plain `OMUFGame` of
`KVAC.Preliminaries.AnonymousTokens.Security` does on the evaluated elements.
An algebraic adversary `A` enters the plain game as `A.forget gen`, which
evaluates the representations `A` submits, and `OMUFAdv_forget` equates the two
advantages with no condition on `A`.

## Where the representations sit

In the plain Figure 6 game the adversary hands the Sign oracle a bare commitment
`C'` and receives the blinded pair `(U', V')`. In the algebraic group model every
group element the adversary *submits* is given by an algebraic representation over
the basis it has seen so far: the fixed elements `G₀, H, X₀, Xᵣ, X⃗` and one
`(αᵤ, αᵥ)` pair per blinded pair issued (O24 Equation 17 for the commitments,
Equation 19 for the forgeries). The representation type is the MAC game's
`AGMRepr`, unchanged: the core shares setup and key generation with the base
MAC, so the fixed basis is the same, and the Sign answers are pairs of group
elements like the MAC codes, so they extend the basis the same way.

The MAC game's Sign oracle takes a message and no group element. Here Sign's
input is a group element, the commitment, given by its representation, the first
issuance request in the repository given that way. That is what the Theorem 5.11
proof needs, since Equation 18 substitutes each commitment's representation into
the server's answer.

## Design notes (Track CMZ-OMUF decisions, September and October 2026)

**Coefficients only.** The Sign oracle evaluates the submitted representation
over the current public elements and issued pairs and answers the resulting
commitment through the core's server algorithm. The Verify oracle and the
winning condition evaluate the token's representations the same way. As in the
MAC game, neither an oracle nor the winning condition compares a representation
with a submitted element (`DESIGN_ALTERNATIVES.md`, *Algebraic adversaries
submit coefficients only*).

**Normalized pair coefficients.** The Sign oracle logs the representation with
its pair-coefficient list cut, or padded with zeros, to exactly one entry per
blinded pair issued so far (`AGMRepr.normalize`). Normalization does not change
the commitment the representation names at its own transcript
(`AGMRepr.eval_normalize`), since `AGMRepr.eval`'s `zipWith` ignores excess
entries and reads missing ones as zero. It buys one guarantee: a logged
representation names the same commitment under any later extension of the
transcript (`AGMRepr.eval_append_of_length_eq`), so the Theorem 5.11 reduction
can read the finished log against one final list of pairs instead of carrying a
per-query prefix. Verify and forgery representations are
evaluated once, against the transcript at the moment they are submitted, and
are not normalized. The comparison with the alternatives is in
`DESIGN_ALTERNATIVES.md`, *Normalized representations in the AGM OMUF game*.

**The log keeps the representations.** Every Sign query is logged in issuance
order as the commitment, its normalized representation, and the server's
answer. The winning condition reads only the log's length and its issued
pairs, but the Theorem 5.11 reduction substitutes each issued
commitment's representation into the polynomial of its answer (Equation 18),
and group elements do not determine the representation the adversary chose, so
the game transcript retains it rather than leaving it to a separate reduction
trace.

**Every Sign query counts.** Figure 6 increments its counter `q` before calling
the server (`q := q + 1`, then `return AT.I.Srv(sk, µ)`), so the counter the
winning condition reads is the log length. The representation basis is the list
of pairs the server issued, read off the log by `AGMOMUFLog.tags`
(`AGMOMUFLog.tags_length_le`). A Sign query issues no pair only when the server
answers `none`, which the core's server `atIssueSrv` never does, so for μCMZ_AT
the two lengths agree. The polynomial bookkeeping of the proof indexes by
issuance.

**Dynamic count here, static budget in the theorems.** As in the plain game and
the MAC games, the oracle carries no query bound. The Theorem 5.11 statements add
a static hypothesis on the adversary (`IsQueryBoundP` over the Sign oracle, at most
`q` queries) so that their `q`-dependent bounds are well-formed.

**The adversary has a private coin oracle.** Its oracle specification is
`unifSpec + AGMOMUFOracleSpec F G n`, as for the plain `OMUFAdversary`, and
`AGM_OMUFGame` answers that oracle in `ProbComp`, leaving the log untouched.
Sampled scalars are not group elements, so they do not extend the
representation basis. The comparison with fixed coins, and with the UF-CMVA
forgers, is in `DESIGN_ALTERNATIVES.md`, *One-more forgers have a private coin
oracle*.

**Carrier.** `ProbComp`, as for the core scheme and the MAC games. The core never
calls a hash, so no random oracle is threaded. The `π_is`-carrying variant of
item 18 lives over `OracleComp (ZKRO H)` and gets its own game.

**Order of the log.** The plain game prepends requests (`μ :: signed`), which is
harmless there because only the length is read. Here the pairs extend the
representation basis in issuance order, so the log appends, as `AGMLog` does.

**What carries over from the MAC track.** The representation type and the
coefficient conversion `AGMRepr.toReprCoeffs` apply to normalized lists as
they are. The MAC track's evaluation bridge `agmRepr_eval_eq_eval_toPoly` does
not, since a blind-issuance answer `(U', V')`, with `V' = (x₀ + xᵣ)·U' + u·C'`, is not a
MAC code on a known message. The Equation 18 bridge is new work for the Theorem 5.11
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
The two oracles of the AGM one-more unforgeability game for μCMZ_AT (O24
Figure 6 against an algebraic adversary, §5.6).
-/
inductive AGMOMUFQuery (F : Type) (n : ℕ) : Type where
  /-- `sign ρ` — an issuance request: the Pedersen commitment `C'` (Figure 9's
  user message, the core sends no `π_iu`) given by its representation over the
  transcript so far (O24 Equation 17). -/
  | sign : AGMRepr F n → AGMOMUFQuery F n
  /-- `verify m⃗ ρ_U ρ_V` — a verification query for the token `(U, V)` on the
  attributes `m⃗`, each component given by its representation. -/
  | verify : (Fin n → F) → AGMRepr F n → AGMRepr F n → AGMOMUFQuery F n

/--
Response types for `AGMOMUFQuery`: the server's blinded pair `(U', V')` for
`sign`, as an `Option`, `none` when the server rejects, as in the plain game; a
Boolean for `verify`.
-/
def AGMOMUFOracleSpec (F G : Type) (n : ℕ) : OracleSpec (AGMOMUFQuery F n)
  | .sign _ => Option (G × G)
  | .verify _ _ _ => Bool

/--
The transcript log threaded through the game: every Sign query in issuance
order, each as the commitment, its normalized representation, and the server's
answer. The log's *length* is Figure 6's query counter `q` (every Sign query
counts); its issued pairs, `AGMOMUFLog.tags`, extend the representation basis;
the representations are kept for the Theorem 5.11 reduction (see *The log keeps
the representations* in the module docstring).
-/
abbrev AGMOMUFLog (F G : Type) (n : ℕ) : Type := List (G × AGMRepr F n × Option (G × G))

/-- The blinded pairs actually issued so far, in issuance order: the issued-pair part of
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
The Sign query as a predicate on the adversary's queries, its private coin oracle
included: the one the static query-budget hypotheses of the Theorem 5.11
statements count, as `IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q` (at
most `q` Sign queries, Verify and coin queries free). Refused Sign queries are
Sign queries.
-/
def AGMOMUFQuery.isSign : ℕ ⊕ AGMOMUFQuery F n → Prop
  | .inl _ => False
  | .inr (.sign _) => True
  | .inr (.verify _ _ _) => False

/-- `IsQueryBoundP` needs the predicate decidable. -/
instance AGMOMUFQuery.instDecidablePredIsSign :
    DecidablePred (AGMOMUFQuery.isSign (F := F) (n := n))
  | .inl _ => isFalse id
  | .inr (.sign _) => isTrue trivial
  | .inr (.verify _ _ _) => isFalse id

/--
One forgery of the algebraic adversary (O24 Equation 19): the attribute vector
`m⃗` and the token `(U, V)` given by one representation per component over the
final transcript. A structure rather than a tuple, so the winning condition and
the Theorem 5.11 proof read named fields.
-/
structure AGMOMUFForgery (F : Type) (n : ℕ) where
  /-- The attribute vector `m⃗`. -/
  msg : Fin n → F
  /-- The representation of `U` over the final transcript. -/
  reprU : AGMRepr F n
  /-- The representation of `V` over the final transcript. -/
  reprV : AGMRepr F n

/--
An algebraic one-more unforgeability adversary against μCMZ_AT for `n`
attributes (O24 §5.6): given the crs `H` and the public parameters
`(X₀, Xᵣ, X⃗)`, it queries a private coin oracle and the Sign and Verify oracles
and outputs its list of forgeries, `q + 1` of them to win. The shape of the
plain `OMUFAdversary`, private coin oracle included (*The adversary has a
private coin oracle* in the module docstring).
-/
structure AGMOMUFAdversary (F G : Type) (n : ℕ) where
  /-- The adversary's program: from `(H, pp)`, query the private coin oracle and
  the Sign and Verify oracles and output the forgeries with their
  representations. -/
  run : G → Params G n →
    OracleComp (unifSpec + AGMOMUFOracleSpec F G n) (List (AGMOMUFForgery F n))

end Data

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-! ## Normalized representations -/

/--
`ρ` with its pair-coefficient list cut, or padded with zeros, to exactly `k`
entries: one per issued pair when `k` is the number of pairs issued so far (see
*Normalized pair coefficients* in the module docstring).
-/
def AGMRepr.normalize (k : ℕ) (ρ : AGMRepr F n) : AGMRepr F n :=
  { ρ with uv := ρ.uv.takeD k (0, 0) }

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- A normalized representation has exactly `k` pair coefficients. -/
@[simp] theorem AGMRepr.normalize_uv_length (k : ℕ) (ρ : AGMRepr F n) :
    (ρ.normalize k).uv.length = k :=
  List.takeD_length _ _ _

/-- Normalizing at the number of issued pairs does not change the element a
representation names, since `zipWith` ignores excess entries and the padding
entries are zero. -/
theorem AGMRepr.eval_normalize (ρ : AGMRepr F n) (g₀ H X₀ Xᵣ : G) (X : Fin n → G)
    (tags : List (G × G)) :
    (ρ.normalize tags.length).eval g₀ H X₀ Xᵣ X tags = ρ.eval g₀ H X₀ Xᵣ X tags := by
  simp only [AGMRepr.eval, AGMRepr.normalize]
  congr 1
  obtain ⟨-, -, -, -, -, uv⟩ := ρ
  dsimp only
  induction tags generalizing uv with
  | nil => simp
  | cons t ts ih =>
      cases uv with
      | nil => simpa using ih []
      | cons c l => simp [ih]

/--
The payoff of normalization (see *Normalized pair coefficients* in the module
docstring): a representation with one pair coefficient per pair in `tags`
evaluates identically over any extension `tags ++ suffix`, since `zipWith`
stops at the shorter list. Lemmas about a commitment logged at an earlier
transcript read its representation through this.
-/
theorem AGMRepr.eval_append_of_length_eq (ρ : AGMRepr F n) (g₀ H X₀ Xᵣ : G) (X : Fin n → G)
    (tags suffix : List (G × G)) (h : ρ.uv.length = tags.length) :
    ρ.eval g₀ H X₀ Xᵣ X (tags ++ suffix) = ρ.eval g₀ H X₀ Xᵣ X tags := by
  rw [AGMRepr.eval, AGMRepr.eval, ← List.append_nil ρ.uv, List.zipWith_append h,
    List.zipWith_nil_left, List.append_nil, List.append_nil]

/-! ## The oracles -/

variable (gen : G)

/--
Honest oracles over the interface `μCMZATCoreSyntax F gen` of the core scheme
(as the MAC game's are over `μCMZBaseMACSyntax`), for the
generator `gen` (a section variable, hence the first explicit argument), the
security parameter, the secret key `sk`, the crs `H`, and the public parameters
`pp = (X₀, Xᵣ, X⃗)`. Noncomputable through the core's sampling.

- `sign ρ` evaluates `ρ` over the issued pairs `tags log` to the commitment
  `C'`, runs the core's `issueSrv` on it, and appends `(C', ρ', answer)` to the
  log, where `ρ'` is `ρ` normalized to `(tags log).length` pair coefficients
  (Figure 6's `q := q + 1`).
- `verify m⃗ ρ_U ρ_V` evaluates both representations over `tags log` and returns
  the core's `verify` on the token they name, leaving the log unchanged.
-/
noncomputable def agmOMUFOracleImpl (secParam : ℕ) (sk : Key F n) (H : G)
    (pp : Params G n) :
    QueryImpl (AGMOMUFOracleSpec F G n) (StateT (AGMOMUFLog F G n) ProbComp)
  | .sign ρ => StateT.mk fun log => do
      let tags := AGMOMUFLog.tags log
      let C' := ρ.evalParams gen H pp tags
      let resp? : Option (G × G) ←
        (μCMZATCoreSyntax F gen).issueSrv (secParam := secParam) H sk C'
      pure (resp?, log ++ [(C', ρ.normalize tags.length, resp?)])
  | .verify m ρU ρV => StateT.mk fun log =>
      let tags := AGMOMUFLog.tags log
      pure ((μCMZATCoreSyntax F gen).verify (secParam := secParam) H sk m
        (ρU.evalParams gen H pp tags, ρV.evalParams gen H pp tags), log)

/-! ## The winning condition, the experiment and the advantage -/

/-- The plain `(m⃗, (U, V))` of a forgery, the token evaluated from its
representations over the issued pairs `tags`: the part the Figure 6 winning
condition `OMUFWins` reads. -/
def AGMOMUFForgery.plain (H : G) (pp : Params G n) (tags : List (G × G))
    (e : AGMOMUFForgery F n) : (Fin n → F) × Code G :=
  (e.msg, (e.reprU.evalParams gen H pp tags, e.reprV.evalParams gen H pp tags))

/--
The winning condition of the AGM OMUF game, read off the final transcript `log`
and the adversary's output `out`: the plain Figure 6 condition `OMUFWins` of
`KVAC.Preliminaries.AnonymousTokens.Security` over the core scheme, with the
query count `q = log.length` (every Sign query counts) and the forgeries
projected to their `(m⃗, (U, V))` over the final issued pairs
`AGMOMUFLog.tags log`. The Theorem 5.11 proof singles out the forgery not
supported by an issued pair by pigeonhole (O24 p. 45). An `abbrev`, like
`OMUFWins`, so the game can `decide` it.
-/
abbrev AGMOMUFWins (secParam : ℕ) (sk : Key F n) (H : G) (pp : Params G n)
    (log : AGMOMUFLog F G n) (out : List (AGMOMUFForgery F n)) : Prop :=
  OMUFWins (μCMZATCoreSyntax F gen) (secParam := secParam) H sk log.length
    -- `(F := F)`: without it, elaboration fails to synthesize
    -- `Field ((μCMZATCoreSyntax F gen).Msg H)`.
    (out.map (AGMOMUFForgery.plain (F := F) gen H pp (AGMOMUFLog.tags log)))

/--
The AGM one-more unforgeability experiment for μCMZ_AT (O24 Figure 6 against
an algebraic adversary, §5.6). Setup and key generation delegate to
`μCMZATCoreSyntax F gen`, as the plain `OMUFGame` delegates to its scheme; the
adversary runs from the empty log with its private coin oracle answered by
`ProbComp` and its Sign and Verify queries by `agmOMUFOracleImpl`; returns `true`
iff `AGMOMUFWins` holds for the final log and the output. Stated for every `n`
and every `secParam` (unused by the core, kept threaded as in the plain game).
`OMUFAdv_forget` equates its advantage with that of `A.forget gen` in the plain
`OMUFGame`.
-/
noncomputable def AGM_OMUFGame (secParam : ℕ) (A : AGMOMUFAdversary F G n) :
    ProbComp Bool := do
  let tok := μCMZATCoreSyntax F gen
  let H : G ← tok.setup secParam n
  let (sk, pp) ← tok.keygen (secParam := secParam) (n := n) H
  -- `HAdd.hAdd` rather than `+`: the binop elaborator's instance search for `+`
  -- times out in the `F`-instance context of this file.
  let impl := HAdd.hAdd
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AGMOMUFLog F G n) ProbComp))
    (agmOMUFOracleImpl gen secParam sk H pp)
  let (out, log) ← (simulateQ impl (A.run H pp)).run []
  pure (decide (AGMOMUFWins gen secParam sk H pp log out))

/-- The AGM OMUF advantage `Pr[= true | AGM_OMUFGame …]`, a function of `secParam`
like `AGM_UF_CMVAAdv`. The Theorem 5.11 statements will bound it under a static
`IsQueryBoundP (A.run H pp) AGMOMUFQuery.isSign q` hypothesis. -/
noncomputable abbrev AGM_OMUFAdv (A : AGMOMUFAdversary F G n) (secParam : ℕ) : ℝ≥0∞ :=
  Pr[= true | AGM_OMUFGame gen secParam A]

/-! ## Forgetting the representations

An algebraic adversary is an adversary of the plain Figure 6 game over the core
scheme: it keeps the pairs the server issues and submits the elements its
representations evaluate to. -/

/-- The queries of the AGM OMUF game as queries of the plain Figure 6 game over the
core scheme, for the crs `H` and the public parameters `pp`, with the pairs issued so
far as state. A coin query is forwarded. `sign ρ` forwards the commitment `ρ`
evaluates to and appends the pair the server issues, if any. `verify m⃗ ρ_U ρ_V`
forwards the token the two representations evaluate to. -/
def agmOMUFQueryToPlain {secParam : ℕ} (H : G) (pp : Params G n) :
    QueryImpl (unifSpec + AGMOMUFOracleSpec F G n)
      (StateT (List (G × G)) (OracleComp
        (unifSpec + OMUFOracleSpec (μCMZATCoreSyntax F gen) (secParam := secParam) (n := n) H)))
  | .inl t => query (spec := unifSpec) t
  | .inr (.sign ρ) => StateT.mk fun tags => do
      let C' := ρ.evalParams gen H pp tags
      -- `resp? : Option (G × G)`: unascribed, `resp?` has type
      -- `Option ((μCMZATCoreSyntax F gen).BlindToken H)`, so `tags ++ resp?.toList` finds
      -- no `HAppend` with `List (G × G)`.
      let resp? : Option (G × G) ← query (spec :=
        OMUFOracleSpec (μCMZATCoreSyntax F gen) (secParam := secParam) (n := n) H) (.sign C')
      pure (resp?, tags ++ resp?.toList)
  | .inr (.verify m ρU ρV) => StateT.mk fun tags => do
      let b ← query (spec :=
        OMUFOracleSpec (μCMZATCoreSyntax F gen) (secParam := secParam) (n := n) H)
        (.verify m (ρU.evalParams gen H pp tags, ρV.evalParams gen H pp tags))
      pure (b, tags)

/-- An algebraic adversary as an adversary of the plain Figure 6 game over the core
scheme. At its own number of attributes `n` it runs `A` through `agmOMUFQueryToPlain`
from no issued pair and evaluates the forgeries over the final pairs
(`AGMOMUFForgery.plain`). At any other number of attributes it outputs no forgery,
which loses. -/
def AGMOMUFAdversary.forget (A : AGMOMUFAdversary F G n) :
    OMUFAdversary (μCMZATCoreSyntax F gen) where
  run {_ n'} :=
    if h : n = n' then h ▸ fun H pp =>
      -- `(F := F)`: without it, elaboration fails to synthesize
      -- `Field ((μCMZATCoreSyntax F gen).Msg H)`.
      (fun z => z.1.map (AGMOMUFForgery.plain (F := F) gen H pp z.2)) <$>
        (simulateQ (agmOMUFQueryToPlain gen H pp) (A.run H pp)).run []
    else fun _ _ => pure []

/-- Forgetting the representations preserves the advantage: the advantage of
`A.forget gen` in the plain Figure 6 game over the core scheme, at `A`'s number of
attributes, is the advantage of `A` in the AGM OMUF game. -/
theorem OMUFAdv_forget (secParam : ℕ) (A : AGMOMUFAdversary F G n) :
    OMUFAdv (μCMZATCoreSyntax F gen) (A.forget gen) secParam n = AGM_OMUFAdv gen A secParam := by
  sorry

end KVAC.Schemes.MicroCMZ
