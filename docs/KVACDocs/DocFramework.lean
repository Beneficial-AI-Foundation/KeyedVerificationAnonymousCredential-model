/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true


#doc (Manual) "Framework — abstract KVAC" =>
%%%
tag := "framework"
%%%

The abstract KVAC framework of O24, Section 4. The four files under
`KVAC/Framework/` mirror Definitions 4.2–4.5 of the paper directly:

- `Syntax.lean` — Definition 4.2 — Track F1.
- `Correctness.lean` — Definition 4.3 — Track F1.
- `Anonymity.lean` — Definition 4.4 — Track F2.
- `Extractability.lean` — Definition 4.5 — Track F2.

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

Parametrised over a credential predicate family that describes which
attributes the holder reveals or proves about.

*TODO (Track F1).* Define the KVAC typeclass or structure mirroring
Definition 4.2. The predicate family should be a parameter so that
extensions (rate-limiting, pseudonyms, time-based policies) can be
instantiated by plugging in a predicate.

:::definition "credential_predicate" (parent := "framework_syntax") (tags := "paper, O24 Def 4.1") (effort := "small") (priority := "high")
*O24 Definition 4.1.* A credential predicate: an efficiently-computable
function on attributes that fixes what a presentation proves.
:::

:::definition "kvac_syntax" (parent := "framework_syntax") (tags := "paper, O24 Def 4.2") (effort := "medium") (priority := "high")
*O24 Definition 4.2.* A keyed-verification credential system
`KVAC = (Setup, KeyGen, Issue, Prove)` for a predicate family
{uses "credential_predicate"}[].
:::

# Correctness (Definition 4.3)

:::group "framework_correctness"
KVAC correctness
:::

An honestly-generated credential, when presented under any predicate it
satisfies, always verifies. The *honestly generated* part is what makes
this a correctness rather than an unforgeability statement.

*TODO (Track F1).* State correctness as a probability bound (or
deterministic equation, if applicable) on the joint output of issuance
and presentation. Definition 4.3.

:::definition "kvac_correctness" (parent := "framework_correctness") (tags := "paper, O24 Def 4.3") (effort := "medium") (priority := "high")
*O24 Definition 4.3.* Correctness for a KVAC scheme {uses "kvac_syntax"}[]:
honestly issued credentials always produce accepting presentations for
the predicates they satisfy.
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

:::definition "extractability_game" (parent := "framework_extract") (tags := "paper, O24 Fig 8") (effort := "medium") (priority := "high")
*O24 Figure 8.* The extractability game for a keyed-verification
credential system, with attribute extractors `Ext.I` and `Ext.P` run
against the adversary's issuance and presentation transcripts.
:::

:::definition "kvac_extractability" (parent := "framework_extract") (tags := "paper, O24 Def 4.5") (effort := "medium") (priority := "high")
*O24 Definition 4.5.* Extractability for a KVAC scheme {uses "kvac_syntax"}[]:
an extractor recovers the certified attributes from any accepting
presentation, in the game of {uses "extractability_game"}[].
:::
