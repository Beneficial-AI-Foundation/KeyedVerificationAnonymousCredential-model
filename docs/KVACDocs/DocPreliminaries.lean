/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal


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
:::

*TODO (Track Pre).* Bind `DL` and `DDH` from VCV-io. Introduce `q-DL`,
`q-DDHI`, and `gap-DL` either project-locally or as upstream
contributions. Each assumption should be stated as an `OracleComp`-based
advantage bound, mirroring VCV-io's existing `DL` / `DDH` shape.

# Zero-knowledge arguments

:::group "pre_zkarg"
Abstract NIZK syntax with the three core properties of O24 Section 3.3:
knowledge soundness, zero-knowledge, and simulation-extractability.
Combined with the generic ZK proof typeclass from the *Core* chapter,
this layer states the properties the schemes need to quote when proving
anonymity and extractability.
:::

*TODO (Track Pre).* State the NIZK properties as predicates over the
generic proof-system typeclass introduced in `KVAC/Core/ZKProof.lean`.
Mirror the definitions of Section 3.3.

# Anonymous tokens

:::group "pre_anontoken"
Anonymous-token syntax and the one-more unforgeability (OMUF) game of
O24 Section 3.4. Anonymous tokens are the headline application of the
OMUF notion — used in the `μCMZ_AT` and `μBBS_AT` chapters of the two
scheme directories.
:::

*TODO (Track Pre).* Define the anonymous-token syntax and the OMUF
security game, mirroring Section 3.4.
