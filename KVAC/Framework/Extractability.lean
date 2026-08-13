/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Framework.Syntax

/-!
# Extraction game for a keyed-verification credential (O24 §4.4, Definition 4.5)

The multi-user man-in-the-middle extraction game `EXT_{KVAC, Ext, A}(λ, n)` of
O24 Figure 8. This file starts with the extractor interface `Ext = (Ext.I, Ext.P)`,
an abstract parameter of the game (Definition 4.5); its μCMZ instantiation from
the ZKP extractors is built in Theorem 5.2.
-/

namespace KVAC.Framework

variable {M : Type → Type} [Monad M]

/-- The extractor `Ext = (Ext.I, Ext.P)` of O24 Definition 4.5, a parameter of
the extraction game rather than a scheme algorithm. Each component recovers an
attribute vector and returns `none` on extraction failure (the paper's abort).
Generic over the carrier `M`, since extraction is pure; the game pins `M` where
it must reduce to `ProbComp`. -/
structure Extractor (kvac : KVACSyntax M) where
  /-- `Ext.I(sk, φ, μ)`: the attribute vector behind an issuance message `μ`. The
  crs is implicit, inferred from `sk`, so this reads as the paper's signature. -/
  extI : {secParam n : Nat} → {crs : kvac.Crs secParam n} →
    kvac.Sk crs → kvac.Pred crs → kvac.IssueMsg crs → Option (kvac.MsgVec crs)
  /-- `Ext.P(sk, φ, ρ)`: the attribute vector behind a presentation message `ρ`. -/
  extP : {secParam n : Nat} → {crs : kvac.Crs secParam n} →
    kvac.Sk crs → kvac.Pred crs → kvac.PresentMsg crs → Option (kvac.MsgVec crs)

end KVAC.Framework
