/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true


#doc (Manual) "μBBS" =>
%%%
tag := "microbbs"
%%%

The second concrete instantiation of the abstract framework,
corresponding to O24, Section 6. μBBS improves on BBDT17 and BBS-MAC:
one fewer group element per signature, alignment with the IETF BBS
draft, and security in the algebraic group model under (q+2)-DL.

Five planned files under `KVAC/Schemes/MicroBBS/` (none landed yet), parallel in structure to
*μCMZ*:

- `Construction.lean` — Section 6.1 — Track BBS-C.
- `AlgebraicMAC.lean` — Section 6.3 — Track BBS-M.
- `Anonymity.lean` — Section 6.4 — Track BBS-A.
- `Extractability.lean` — Section 6.5 — Track BBS-E.
- `OneMoreUnforgeability.lean` — Section 6.6 — Track BBS-OMUF.

*Note on curves.* Ristretto255 is *not* a valid concrete instance for
μBBS — μBBS requires a curve larger than Ristretto255 (at least 384-bit)
for 128-bit security under q-DL. μBBS is out of v1 example scope; see
the *Concrete run* chapter.

# Construction (Section 6.1)

:::group "bbs_construction"
The four protocol algorithms: `KeyGen`, `Setup`, `Issue`, and `Present`.
Like *μCMZ Construction*, stated over the abstract group API
(`SampleableGroup F G`; setup and tag bases sample group elements).
:::

*TODO (Track BBS-C).* Implement the four algorithms following Section
6.1.

# Algebraic-MAC security (Section 6.3)

:::group "bbs_amac"
*Theorems 6.1 and 6.5, via Lemmas 6.8 and 6.9.* μBBS, viewed as an
algebraic MAC under the *Core* algebraic-MAC interface, is UF-CMVA in
the algebraic group model under (q+2)-DL. The proof requires the DDH-oracle augmentation in the
algebraic-MAC unforgeability game — one of the technical contributions
of O24.
:::

*TODO (Track BBS-M).* State and prove Theorems 6.6, 6.8, 6.9. The
DDH-oracle augmentation may need to be threaded through the *Core*
algebraic-MAC interface; coordinate with Track 0 if so.

# Anonymity (Section 6.4)

:::group "bbs_anonymity"
The analogue of Theorem 5.8 for μBBS. Carries a technical caveat: μBBS
loses anonymity on messages satisfying the relation in O24 Section 6,
Equation 7. The statement either restricts the message space accordingly
or quantifies *anonymous except on a negligible message set*.
:::

*TODO (Track BBS-A).* State and prove the anonymity theorem. Document
the Section 6 Equation 7 caveat in the formal statement, not in a
footnote.

# Extractability (Section 6.5)

:::group "bbs_extract"
μBBS is extractable in the algebraic group model. The proof uses
straight-line extraction (from the *Proof systems* chapter) plus the
DDH-oracle-augmented MAC unforgeability result.
:::

*TODO (Track BBS-E).* State and prove the extractability theorem.

# One-more unforgeability (Section 6.6)

:::group "bbs_omuf"
*Theorem 6.7.* The anonymous-token variant `μBBS_AT` is one-more
unforgeable. Lemma 6.12 and Corollary 6.13 give a Cheon-style attack
recovering the key in time `O(√(p/d) + √d)` for a divisor `d` of
`p ± 1`, costing roughly 20 bits of security relative to the
algebraic-group bound; the statement should reflect this.
:::

*TODO (Track BBS-OMUF).* State and prove Theorem 6.12.
