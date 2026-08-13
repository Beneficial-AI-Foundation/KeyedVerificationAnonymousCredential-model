/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Framework.Syntax
import VCVio.OracleComp.ProbComp

/-!
# Extraction game for a keyed-verification credential (O24 §4.4, Definition 4.5)

The multi-user man-in-the-middle extraction game `EXT_{KVAC, Ext, A}(λ, n)` of
O24 Figure 8. The extractor `Ext = (Ext.I, Ext.P)` is an abstract parameter of
the game (Definition 4.5); its μCMZ instantiation from the ZKP extractors is
built in Theorem 5.2.
-/

namespace KVAC.Framework

open OracleComp OracleSpec

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

/-! ## The four oracles of Figure 8 -/

/-- The oracle calls of the O24 Figure 8 extraction game, for a fixed crs.
`newUsr m⃗` creates an honest user, `issue φ μ` is the server's issuance response
to a user message `μ`, `presentUsr i φ` is honest user `i`'s presentation, and
`present φ ρ` is the server's presentation check. -/
inductive EXTQuery (kvac : KVACSyntax M) {secParam n : Nat}
    (crs : kvac.Crs secParam n) : Type where
  | newUsr     : kvac.MsgVec crs → EXTQuery kvac crs
  | issue      : kvac.Pred crs → kvac.IssueMsg crs → EXTQuery kvac crs
  | presentUsr : Nat → kvac.Pred crs → EXTQuery kvac crs
  | present    : kvac.Pred crs → kvac.PresentMsg crs → EXTQuery kvac crs

/-- Answer types of the Figure 8 oracles: `newUsr` returns the new user index
`ctr`, `issue` the blinded credential or `⊥` (`Option`), `presentUsr` the
presentation message or `none` on an out-of-range index, `present` the accept
bit. -/
def EXTOracleSpec (kvac : KVACSyntax M) {secParam n : Nat}
    (crs : kvac.Crs secParam n) : OracleSpec (EXTQuery kvac crs)
  | .newUsr _       => Nat
  | .issue _ _      => Option (kvac.BlindCred crs)
  | .presentUsr _ _ => Option (kvac.PresentMsg crs)
  | .present _ _    => Bool

/-! ## The game state -/

/-- The game state carried through the O24 Figure 8 oracles for a fixed crs.
`qrs` is the list of attribute vectors extracted from accepted issuance queries
(the paper's `Qrs`), `pqrs` the honestly presented `(φ, ρ)` pairs (`PQrs`), and
`usrs` the honest users `(m, σ)` in creation order (`Usrs`, so the index a
`newUsr` query returns is this list's length at creation). Figure 8's `Issue`
abort is not a field here: the oracle implementation raises it as an exception in
the oracle monad, which the game counts as an adversary win. Generic over the
carrier `M`. -/
structure EXTState (kvac : KVACSyntax M) {secParam n : Nat}
    (crs : kvac.Crs secParam n) where
  /-- `Qrs`: attribute vectors extracted from accepted issuance queries. -/
  qrs : List (kvac.MsgVec crs)
  /-- `PQrs`: `(predicate, presentation)` pairs produced by honest users. -/
  pqrs : List (kvac.Pred crs × kvac.PresentMsg crs)
  /-- `Usrs`: honest users `(m, σ)`, indexed by creation order. -/
  usrs : List (kvac.MsgVec crs × kvac.Cred crs)

/-- The initial game state, all logs empty. -/
def EXTState.empty (kvac : KVACSyntax M) {secParam n : Nat}
    (crs : kvac.Crs secParam n) : EXTState kvac crs :=
  ⟨[], [], []⟩

end KVAC.Framework
