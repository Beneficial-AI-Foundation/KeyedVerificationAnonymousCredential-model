/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Algebraic message authentication code (Track 0)

Abstract typeclass for algebraic MACs over a prime-order group, following
Definition 3.1 of Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint 2024/1552.

An algebraic MAC `MAC = (S, K, M, V)` for `n` attributes over a message family
`𝕄 = {𝕄_λ}_λ` consists of a setup algorithm, a key-generation algorithm, a
MAC algorithm, and a deterministic verification algorithm. The MAC must
satisfy correctness (every honestly generated MAC verifies) and unforgeability
under chosen-message and verification attacks (UF-CMVA).

See `docs/PLAN.md` for the design intent and `docs/STYLE_GUIDE.md` for the
expected file layout.
-/

namespace KVAC.Core

-- TODO(Track 0): define the algebraic MAC typeclass and the UF-CMVA security
-- game here, mirroring Definition 3.1 and Figure 5 of O24.

end KVAC.Core
