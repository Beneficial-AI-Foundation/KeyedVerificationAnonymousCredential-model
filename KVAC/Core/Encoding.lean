/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

/-!
# Reversible message encoding (Track 0)

Abstract `Encodable` typeclass for the paper's `EncodeToG` / `DecodeFromG`
(CPZ19 §2.1, §6). Captures the multi-valued nature of decoding: a single group
element typically corresponds to several candidate plaintexts, and the
round-trip property selects the canonical one.

The concrete realization of `EncodeToG` in `signalapp/libsignal` relies on
Elligator-inverse, which is the upstream contribution tracked as Track A in
[`curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify).

See `docs/PLAN.md` for the design intent.
-/

namespace KVAC.Core

-- TODO(Track 0): define the `Encodable` typeclass here.

end KVAC.Core
