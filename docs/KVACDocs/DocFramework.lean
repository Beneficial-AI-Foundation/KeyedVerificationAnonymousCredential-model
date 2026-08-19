/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Framework

open Verso.Genre Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true


#doc (Manual) "Framework — abstract KVAC" =>
%%%
tag := "framework"
%%%

The abstract KVAC framework of O24, Section 4. The files under
`KVAC/Framework/` mirror Definitions 4.1–4.5 of the paper directly, and
`KVAC/Framework.lean` is the umbrella that bundles the syntax with a
correctness proof:

- `PredicateFamily.lean` — Definition 4.1 — Track F1, landed.
- `Syntax.lean` — Definition 4.2 — Track F1, landed.
- `Correctness.lean` — Definition 4.3 — Track F1, landed.
- `Anonymity.lean` — Definition 4.4 — Track F2, not yet written.
- `Extractability.lean` — Definition 4.5 — Track F2, not yet written.

The definitions are *scheme-agnostic* — both μCMZ and μBBS prove their
constructions satisfy these same paper-level statements, which is the
formalisation-correctness guarantee of the framework. The recommendation
from `docs/PLAN.md` is to drive these definitions from O24 Section 4
directly rather than from μCMZ's algebra; if the typeclass shapes mirror
the paper, μBBS will fit without contortions.

# Syntax (Definition 4.2)

:::group "framework_syntax"
KVAC syntax
:::

A KVAC scheme is a tuple of algorithms `(S, K, I, P)`:

- `S` — system setup,
- `K` — issuer key generation,
- `I` — interactive issuance, parametrised by a credential predicate,
- `P` — presentation.

The credential predicate family, describing which attributes the holder
reveals or proves about, is a structure that the syntax extends rather
than a parameter it takes. Extensions (rate-limiting, pseudonyms,
time-based policies) are therefore realised by the `Pred` type and
`holds` semantics a scheme supplies in its own instance.

:::definition "credential_predicate" (lean := "KVAC.Framework.PredicateFamily, KVAC.Framework.PredicateFamily.instDecidableEqPred") (parent := "framework_syntax") (tags := "paper, O24 Def 4.1")
*O24 Definition 4.1.* A credential predicate family: a per-CRS type of
predicate descriptions `Pred` with Boolean semantics `holds`, containing
the trivial predicate `φ₁` and closed under conjunction. Extends
{uses "keyed_setup"}[], because Definition 4.2 has the setup implicitly
define both the attribute space and the family.
Beyond Definition 4.1 the structure carries two game-support fields, the
exact-attribute predicate `φ_m⃗` that Figure 8's `NewUsr` oracle needs as
data, and decidable equality on predicate descriptions.
:::

:::definition "kvac_syntax" (lean := "KVAC.Framework.KVACSyntax, KVAC.Framework.KVACSyntax.instDecidableEqPresentMsg, KVAC.Framework.KVACSyntax.issue, KVAC.Framework.KVACSyntax.present, KVAC.Framework.KVACSyntax.mac") (parent := "framework_syntax") (tags := "paper, O24 Def 4.2")
*O24 Definition 4.2.* A keyed-verification credential system
`KVAC = (S, K, I, P)` for a predicate family
{uses "credential_predicate"}[]. Each one-round protocol is split into
its non-interactive moves as the paper does, issuance into `issueUsr₁`,
`issueSrv`, and `issueUsr₂`, presentation into `presentUsr` and
`presentSrv`. Both rejections are carried by `Option`, the issuer's
`σ' = ⊥` of this definition and the user's abort on the `check` lines of
Figure 9. The derived `issue` and `present` chain those moves into the
full interactions, generalising the paper's `KVAC.M` and `KVAC.V`
shorthands from `φ_m⃗` to an arbitrary predicate. The further shorthand
`mac` is the paper's `KVAC.M(sk, m⃗)` itself, `issue` specialised to the
exact-attribute predicate `φ_m⃗`.
:::

# Correctness (Definition 4.3)

:::group "framework_correctness"
KVAC correctness
:::

An honestly-generated credential, when presented under any predicate it
satisfies, always verifies. The *honestly generated* part is what makes
this a correctness rather than an unforgeability statement.

Definition 4.3 already quantifies over the supports of setup and key
generation, and `Correct` follows it there. Where it departs is the
experiment itself: the paper asks that presentation accept with
probability overwhelming in λ, whereas `Correct` quantifies over the
supports of `issue` and `present` and so demands probability one. That
strengthening is faithful for the perfectly-correct schemes here and
matches the algebraic MAC layer.

*TODO (Tracks CMZ-C, BBS-C).* The same definition also restricts the
predicate family to one containing every partial-disclosure predicate
`φ_a⃗`. The abstract family supplies the full-disclosure member `φ_m⃗` as
the `exactPred` field, but not the wildcard members. `Correct` is stated for all `φ` and `φ'`, so
it never needs them to exist. Exhibiting them is a scheme-level
obligation, discharged when μCMZ and μBBS build their predicate-family
instances.

:::definition "kvac_correctness" (lean := "KVAC.Framework.Correct, KVAC.Framework.KVAC, KVAC.Framework.CorrectOutcome, KVAC.Framework.RunSem, KVAC.Framework.GenCorrect, KVAC.Framework.probRunSem, KVAC.Framework.roRunSem, KVAC.Framework.CorrectRO") (parent := "framework_correctness") (tags := "paper, O24 Def 4.3")
*O24 Definition 4.3.* Correctness for a KVAC scheme {uses "kvac_syntax"}[]:
honestly issued credentials always produce accepting presentations for
the predicates they satisfy. Stated as two halves, issuance never
rejects or aborts and presentation always accepts, so downstream proofs
can cite each. The bundled object `KVAC` pairs the syntactic algorithms
over `ProbComp` with a correctness proof, as O24 Definition 4.2 closes.
:::

# Anonymity (Definition 4.4)

:::group "framework_anonymity"
KVAC anonymity
:::

The real-vs-simulated indistinguishability game. The notion has two
variants O24 distinguishes:

- *Statistical anonymity* — indistinguishability holds against unbounded
  adversaries; μCMZ achieves this.
- *Everlasting forward anonymity* — indistinguishability holds even
  against an adversary who later learns the issuer's secret key;
  relevant for μBBS.

Anonymity requires a simulator that can produce indistinguishable
transcripts for both issuance and presentation.

*TODO (Track F2).* Define the anonymity game and the two variants. Use
the `SampleableGroup` typeclass from the *Core* chapter
(game-construction binders).

:::definition "kvac_anonymity" (parent := "framework_anonymity") (tags := "paper, O24 Def 4.4") (effort := "medium") (priority := "high")
*O24 Definition 4.4.* Anonymity for a KVAC scheme {uses "kvac_syntax"}[]:
issuance and presentation are simulatable without the secret attributes,
so presentations are unlinkable across executions.
:::

# Extractability (Definition 4.5)

:::group "framework_extract"
KVAC extractability
:::

The multi-user man-in-the-middle extractability game. The extractor must
recover the attributes from any successful issuance or presentation
transcript, including in settings where the adversary mediates between
honest parties. The lemma that this implies the original CMZ14
single-user unforgeability is included as a sanity check.

*TODO (Track F2).* Define the extractability game (Definition 4.5) and
prove the reduction to CMZ14 unforgeability as a corollary.

:::definition "extractability_game" (lean := "KVAC.Framework.Extractor, KVAC.Framework.EXTQuery, KVAC.Framework.EXTOracleSpec, KVAC.Framework.EXTState, KVAC.Framework.EXTState.empty, KVAC.Framework.EXTComp, KVAC.Framework.liftRO, KVAC.Framework.getEXTState, KVAC.Framework.modifyEXTState, KVAC.Framework.extOracleImpl") (parent := "framework_extract") (tags := "paper, O24 Fig 8") (effort := "medium") (priority := "high")
*O24 Figure 8.* The extractability game for a keyed-verification
credential system, with attribute extractors `Ext.I` and `Ext.P` run
against the adversary's issuance and presentation transcripts.
:::

:::definition "kvac_extractability" (parent := "framework_extract") (tags := "paper, O24 Def 4.5") (effort := "medium") (priority := "high")
*O24 Definition 4.5.* Extractability for a KVAC scheme {uses "kvac_syntax"}[]:
an extractor recovers the certified attributes from any accepting
presentation, in the game of {uses "extractability_game"}[].
:::
