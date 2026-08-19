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

/-! ## The oracle monad and its plumbing -/

/-- The monad the O24 Figure 8 oracles run in: the shared random-oracle cache and
the game state `EXTState` carried in one `StateT`, over `ExceptT Unit` (the
`Issue` abort, read as an adversary win) over `ProbComp`. -/
abbrev EXTComp (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    {secParam n : Nat} (crs : kvac.Crs secParam n) : Type → Type :=
  StateT (H.spec.QueryCache × EXTState kvac crs) (ExceptT Unit ProbComp)

/-- Lift a credential computation into the oracle monad: run it against the shared
random-oracle table via `runRO`, write the table back, leave the game state alone.

IMPORTANT. This is the single site of the cache plumbing the whole game depends
on. It projects the cache out of the state, runs the credential algorithm at the
`ProbComp` layer, and threads the updated cache back, so all four Figure 8 oracles
share one random-oracle table and a Fiat–Shamir credential's proofs stay
consistent. Get this threading wrong and the shared-oracle semantics break
silently. The carrier reconciliation that governs it is tracked in issue #118. -/
def liftRO {α : Type} (H : HashSpec) {kvac : KVACSyntax (OracleComp (ZKRO H))}
    {secParam n : Nat} {crs : kvac.Crs secParam n} (c : OracleComp (ZKRO H) α) :
    EXTComp H kvac crs α :=
  StateT.mk fun (cache, st) => do
    let (a, cache') ← runRO H cache c
    pure (a, (cache', st))

/-- Read the `EXTState` half of the game state, leaving the cache implicit. -/
def getEXTState (H : HashSpec) {kvac : KVACSyntax (OracleComp (ZKRO H))}
    {secParam n : Nat} {crs : kvac.Crs secParam n} :
    EXTComp H kvac crs (EXTState kvac crs) :=
  Prod.snd <$> get

/-- Update the `EXTState` half of the game state, leaving the cache untouched. -/
def modifyEXTState (H : HashSpec) {kvac : KVACSyntax (OracleComp (ZKRO H))}
    {secParam n : Nat} {crs : kvac.Crs secParam n}
    (f : EXTState kvac crs → EXTState kvac crs) : EXTComp H kvac crs Unit :=
  modify fun (cache, st) => (cache, f st)

/-! ## The oracle implementation -/

/-- The Figure 8 oracle implementation over the carrier `OracleComp (ZKRO H)`.
Each credential algorithm runs through `liftRO` on the shared table, so a
Fiat–Shamir credential's proofs share one random oracle. The `Issue` abort of
Figure 8 is `throw ()` in the `ExceptT Unit` layer, short-circuiting the run; the
game reads a thrown abort as an adversary win. -/
def extOracleImpl (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (ext : Extractor kvac) {secParam n : Nat} (crs : kvac.Crs secParam n)
    (sk : kvac.Sk crs) (pp : kvac.Pp crs) :
    QueryImpl (EXTOracleSpec kvac crs) (EXTComp H kvac crs)
  -- Figure 8  Oracle NewUsr(m): σ ← KVAC.M(sk, m); Usrs[ctr] := (m, σ);
  -- return (ctr := ctr + 1). Runs the honest MAC `kvac.mac`; on a credential it
  -- appends (m, σ) to `usrs` and answers with the pre-append length (the new
  -- user's index).
  -- The `none` arm below is the honest-issuance failure. On the happy trace it
  -- never fires: for a correct scheme, issuance under the exact-attribute
  -- predicate `φ_m` always yields `some` (`Correct` specialised at `φ = φ_m` via
  -- `holds_exactPred`), so `usrs` always grows and the counter matches the
  -- paper's unconditional `ctr := ctr + 1`. Proving the `none` case unreachable
  -- (hence that the happy trace is the only outcome) needs `Correct` lifted to
  -- the `OracleComp (ZKRO H)` carrier (issue #118) and is deferred to PR #138.
  | .newUsr m => do
      match ← liftRO H (kvac.mac crs sk pp m) with
      | none   => return (← getEXTState H).usrs.length
      | some σ =>
        let i := (← getEXTState H).usrs.length
        modifyEXTState H fun st => { st with usrs := st.usrs ++ [(m, σ)] }
        return i
  -- Figure 8  Oracle Issue(φ, µ): σ' ← KVAC.I.Srv(sk, φ, µ); if σ' = ⊥ return ⊥;
  -- m := Ext.I(sk, φ, µ); if φ(m) = 0 abort; Qrs := Qrs ∪ {m}; return σ'. On ⊥
  -- it answers `none`; otherwise it applies the pure extractor `Ext.I`, aborts
  -- with `throw ()` if extraction fails or `φ(m) = 0` (the game counts it a win),
  -- else records `m` in `qrs` and answers with σ'.
  | .issue φ μ => do
      match ← liftRO H (kvac.issueSrv crs sk φ μ) with
      | none    => return none
      | some σ' =>
        match ext.extI sk φ μ with
        | none   => throw ()
        | some m =>
          if kvac.holds crs φ m then
            modifyEXTState H fun st => { st with qrs := st.qrs ++ [m] }
            return some σ'
          else throw ()
  -- Figure 8  Oracle PresentUsr(i, φ): (m, σ) := Usrs[i];
  -- ρ ← KVAC.P.Usr(pp, m, σ, φ); PQrs := PQrs ∪ {(φ, ρ)}; return ρ. An
  -- out-of-range index answers `none`; otherwise it runs the honest presentation,
  -- records `(φ, ρ)` in `pqrs`, and answers with ρ.
  | .presentUsr i φ => do
      match (← getEXTState H).usrs[i]? with
      | none        => return none
      | some (m, σ) =>
        let ρ ← liftRO H (kvac.presentUsr crs pp m σ φ)
        modifyEXTState H fun st => { st with pqrs := st.pqrs ++ [(φ, ρ)] }
        return some ρ
  -- Figure 8  Oracle Present(φ, ρ): return KVAC.P.Srv(sk, φ, ρ). Runs the server
  -- presentation check and answers with the accept bit; records nothing.
  | .present φ ρ => liftRO H (kvac.presentSrv crs sk φ ρ)

end KVAC.Framework
