/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal


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
A KVAC scheme is a tuple of algorithms `(S, K, I, P)`:

- `S` — system setup,
- `K` — issuer key generation,
- `I` — interactive issuance, parametrised by a credential predicate,
- `P` — presentation.

Parametrised over a credential predicate family that describes which
attributes the holder reveals or proves about.
:::

*TODO (Track F1).* Define the KVAC typeclass or structure mirroring
Definition 4.2. The predicate family should be a parameter so that
extensions (rate-limiting, pseudonyms, time-based policies) can be
instantiated by plugging in a predicate.

# Correctness (Definition 4.3)

:::group "framework_correctness"
An honestly-generated credential, when presented under any predicate it
satisfies, always verifies. The *honestly generated* part is what makes
this a correctness rather than an unforgeability statement.
:::

*TODO (Track F1).* State correctness as a probability bound (or
deterministic equation, if applicable) on the joint output of issuance
and presentation. Definition 4.3.

# Anonymity (Definition 4.4)

:::group "framework_anonymity"
The real-vs-simulated indistinguishability game. The notion has two
variants O24 distinguishes:

- *Statistical anonymity* — indistinguishability holds against unbounded
  adversaries; μCMZ achieves this.
- *Everlasting forward anonymity* — indistinguishability holds even
  against an adversary who later learns the issuer's secret key;
  relevant for μBBS.

Anonymity requires a simulator that can produce indistinguishable
transcripts for both issuance and presentation.
:::

*TODO (Track F2).* Define the anonymity game and the two variants. Use
the `SampleableGroup` typeclass from the *Core* chapter
(game-construction binders).

# Extractability (Definition 4.5)

:::group "framework_extract"
The multi-user man-in-the-middle extractability game. The extractor must
recover the attributes from any successful issuance or presentation
transcript, including in settings where the adversary mediates between
honest parties. The lemma that this implies the original CMZ14
single-user unforgeability is included as a sanity check.
:::

*TODO (Track F2).* Define the extractability game (Definition 4.5) and
prove the reduction to CMZ14 unforgeability as a corollary.
