/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Generic NIZK proof system (Track 0)

Abstract typeclass for non-interactive zero-knowledge proof systems following
the syntax of Section 3.3 of Orrù, *Revisiting Keyed-Verification Anonymous
Credentials*, IACR ePrint 2024/1552.

A proof system `ZKP = (S, P, V)` over a relation family `R` consists of a setup
algorithm producing a common-reference string `crs`, a prover taking
`(crs, x, w) ∈ R`, and a verifier taking `(crs, x, π)`. Properties:

- completeness;
- knowledge soundness (existence of an extractor recovering the witness);
- zero-knowledge (existence of a simulator);
- (optionally) simulation-extractability — knowledge soundness even when the
  adversary has access to simulated proofs.

See `docs/PLAN.md` for the design intent and `docs/STYLE_GUIDE.md` for the
expected file layout.
-/

namespace KVAC.Core

-- TODO(Track 0): define the ZK proof system typeclass and its security
-- predicates here, mirroring Section 3.3 of O24.

end KVAC.Core
