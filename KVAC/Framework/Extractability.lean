/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Framework.Syntax
import KVAC.Core.NIZKP.Security
import VCVio.OracleComp.ProbComp

/-!
# Extraction game for a keyed-verification credential (O24 §4.4, Definition 4.5)

The multi-user man-in-the-middle extraction game `EXT_{KVAC, Ext, A}(λ, n)` of
O24 Figure 8. The extractor `Ext = (Ext.I, Ext.P)` is an abstract parameter of
the game (Definition 4.5); its μCMZ instantiation from the ZKP extractors is
built in Theorem 5.10.
-/

namespace KVAC.Framework

open OracleComp OracleSpec KVAC.Core

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
`newUsr m` creates an honest user, `issue φ μ` is the server's issuance response
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
`usrs` the honest users `(m, σ)` in creation order (`Usrs`). Figure 8 writes the
user counter update as `ctr := ctr + 1`; we read a `newUsr` query as returning
the index just written (this list's length at creation), the only reading under
which `usrs[i]` resolves to that user. Figure 8's `Issue`
abort is not a field here: the oracle implementation raises it as an exception in
the oracle monad (`ExceptT`), which the game counts as an adversary win. Generic
over the carrier `M`. -/
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

/-! ## Running credential algorithms against the random oracle -/

/-- Run a credential computation against the random oracle, from the table
`cache`, and return its result together with the updated table. -/
def runRO {α : Type} (H : HashSpec) (cache : H.spec.QueryCache)
    (c : OracleComp (ZKRO H) α) : ProbComp (α × H.spec.QueryCache) :=
  (simulateQ (zkROImpl H) c).run cache

/-! ## The oracle implementation -/

/-- The Figure 8 oracle implementation over the carrier `OracleComp (ZKRO H)`.
Each credential algorithm runs through `runRO` on the shared table, which is
carried alongside the game state, so a Fiat–Shamir credential's proofs share one
random oracle. The `Issue` abort of Figure 8 is `throw ()` in the `ExceptT Unit`
layer of the target monad, short-circuiting the run; the game reads a thrown
abort as an adversary win. -/
def extOracleImpl (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (ext : Extractor kvac) {secParam n : Nat} (crs : kvac.Crs secParam n)
    (sk : kvac.Sk crs) (pp : kvac.Pp crs) :
    QueryImpl (EXTOracleSpec kvac crs)
      (StateT (H.spec.QueryCache × EXTState kvac crs) (ExceptT Unit ProbComp))
  -- Figure 8  Oracle NewUsr(m):
  --   σ ← KVAC.M(sk, m)
  --   Usrs[ctr] := (m, σ)
  --   return (ctr := ctr + 1)
  -- Implementation. Runs the honest MAC KVAC.M(sk, m), which is `kvac.mac`,
  -- against the random oracle. When a credential `σ` results it appends (m, σ)
  -- to `usrs`, whose length is the counter `ctr`, and answers with the length
  -- before the append, the new user's index. Honest issuance may fail (`none`),
  -- and then no user is recorded.
  | .newUsr m => StateT.mk fun (cache, st) => do
      let (σ?, cache') ← runRO H cache (kvac.mac crs sk pp m)
      match σ? with
      | none   => pure (st.usrs.length, (cache', st))
      | some σ => pure (st.usrs.length, (cache', { st with usrs := st.usrs ++ [(m, σ)] }))
  -- Figure 8  Oracle Issue(φ, µ):
  --   σ' ← KVAC.I.Srv(sk, φ, µ)
  --   if σ' = ⊥ : return ⊥
  --   m := Ext.I(sk, φ, µ)
  --   if φ(m) = 0 : abort
  --   Qrs := Qrs ∪ {m}
  --   return σ'
  -- Implementation. Runs the server issuance `kvac.issueSrv` against the random
  -- oracle. On ⊥ it answers `none`. Otherwise it applies the extractor `Ext.I`,
  -- a pure step. If extraction fails, or returns `m` with `φ(m) = 0`, it aborts
  -- the run with `throw ()` (Figure 8's `abort`), which the game counts as an
  -- adversary win. Otherwise it adds `m` to `qrs` (the paper's Qrs) and answers
  -- with the credential σ'.
  | .issue φ μ => StateT.mk fun (cache, st) => do
      let (σ'?, cache') ← runRO H cache (kvac.issueSrv crs sk φ μ)
      match σ'? with
      | none    => pure (none, (cache', st))
      | some σ' =>
        match ext.extI sk φ μ with
        | none   => throw ()
        | some m =>
          if kvac.holds crs φ m
          then pure (some σ', (cache', { st with qrs := st.qrs ++ [m] }))
          else throw ()
  -- Figure 8  Oracle PresentUsr(i, φ):
  --   (m, σ) := Usrs[i]
  --   ρ ← KVAC.P.Usr(pp, m, σ, φ)
  --   PQrs := PQrs ∪ {(φ, ρ)}
  --   return ρ
  -- Implementation. Reads honest user `i` from `usrs`. For an index past the end
  -- it answers `none`. Otherwise it runs the honest presentation `kvac.presentUsr`
  -- against the random oracle, records `(φ, ρ)` in `pqrs` (the paper's PQrs), and
  -- answers with ρ.
  | .presentUsr i φ => StateT.mk fun (cache, st) =>
      match st.usrs[i]? with
      | none        => pure (none, (cache, st))
      | some (m, σ) => do
          let (ρ, cache') ← runRO H cache (kvac.presentUsr crs pp m σ φ)
          pure (some ρ, (cache', { st with pqrs := st.pqrs ++ [(φ, ρ)] }))
  -- Figure 8  Oracle Present(φ, ρ):
  --   return KVAC.P.Srv(sk, φ, ρ)
  -- Implementation. Runs the server presentation check `kvac.presentSrv` against
  -- the random oracle and answers with the accept bit. It records nothing.
  | .present φ ρ => StateT.mk fun (cache, st) => do
      let (b, cache') ← runRO H cache (kvac.presentSrv crs sk φ ρ)
      pure (b, (cache', st))

end KVAC.Framework
