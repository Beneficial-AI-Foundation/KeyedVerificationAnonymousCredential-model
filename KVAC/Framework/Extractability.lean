/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Framework.Syntax
import KVAC.Core.NIZKP.Security
import VCVio.OracleComp.ProbComp
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Extraction game for a keyed-verification credential (O24 §4.4, Definition 4.5)

The multi-user man-in-the-middle extraction game `EXT_{KVAC, Ext, A}(λ, n)` of
O24 Figure 8. The extractor `Ext = (Ext.I, Ext.P)` is an abstract parameter of
the game (Definition 4.5); its μCMZ instantiation from the ZKP extractors is
built in Theorem 5.10.
-/

namespace KVAC.Framework

open OracleComp OracleSpec KVAC.Core ENNReal

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

/-! ## The adversary -/

/-- The full oracle interface an extraction adversary sees for a fixed crs: the
four Figure 8 oracles together with the random oracle `ZKRO H`.

Formalizes the oracle access of `A^{Issue, Present, NewUsr, PresentUsr}` in O24
Figure 8. The random oracle is included because the issuance and presentation
messages the adversary submits embed Fiat–Shamir proofs, so it queries the same
`H` the honest oracles use; the game runs both halves on one shared table. -/
abbrev EXTAdvSpec (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    {secParam n : Nat} (crs : kvac.Crs secParam n) :
    OracleSpec (EXTQuery kvac crs ⊕ (ℕ ⊕ H.Dom)) :=
  EXTOracleSpec kvac crs + ZKRO H

/-- An extraction adversary (O24 Figure 8): given the public parameters `pp`, it
queries the four extraction oracles and the random oracle, and outputs the
challenge `(φ*, ρ*)`, a predicate and a presentation message. The crs is passed
alongside `pp`, matching `UFAdversary`; the paper infers it from `pp`. -/
structure EXTAdversary (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H))) where
  run : {secParam n : Nat} → (crs : kvac.Crs secParam n) → kvac.Pp crs →
    OracleComp (EXTAdvSpec H kvac crs) (kvac.Pred crs × kvac.PresentMsg crs)

/-! ## The game -/

/-- The random-oracle handler over the game's combined state. The adversary's
direct `ZKRO H` queries must hit the same table the honest oracles use, so this
runs `zkROImpl H` on the `cache` component of the shared `(cache × EXTState)`
state, leaving the game state and the `ExceptT` abort transformer untouched. It is
the `ZKRO H` half of the game's `QueryImpl`, added to `extOracleImpl`. -/
def extROImpl (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    {secParam n : Nat} (crs : kvac.Crs secParam n) :
    QueryImpl (ZKRO H)
      (StateT (H.spec.QueryCache × EXTState kvac crs) (ExceptT Unit ProbComp)) :=
  fun q => StateT.mk fun (cache, st) => do
    let (a, cache') ← (zkROImpl H q).run cache
    pure (a, (cache', st))

/-- The O24 Figure 8 extraction game `EXT_{KVAC, Ext, A}(λ, n)` as a `ProbComp Bool`.

Samples `crs` and `(sk, pp)` against a fresh random-oracle table, then runs the
adversary through the four extraction oracles (`extOracleImpl`) and the shared
random oracle (`extROImpl`), carrying one table across both halves. A Figure 8
`Issue` abort surfaces as `Except.error` and is an adversary win. Otherwise the
challenge `(φ*, ρ*)` wins when the presentation verifies, `(φ*, ρ*)` was not an
honest presentation (`∉ PQrs`), and the extracted `m* := Ext.P(sk, φ*, ρ*)` was
never issued (`∉ Qrs`) or fails `φ*`. A failed `Ext.P` (its `none`) counts as the
last disjunct, matching the abort convention for `Ext.I`. -/
def EXTGame (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (ext : Extractor kvac) (A : EXTAdversary H kvac) (secParam n : Nat) :
    ProbComp Bool := do
  let (crs, cache₁) ← runRO H ∅ (kvac.setup secParam n)
  let ((sk, pp), cache₂) ← runRO H cache₁ (kvac.keygen crs)
  -- `oracles` is the superscript `^{Issue, Present, NewUsr, PresentUsr}`, the four
  -- extraction oracles and the shared random oracle answering the adversary's queries
  -- over one table, run from the post-keygen cache and the empty game state.
  let oracles := extOracleImpl H kvac ext crs sk pp + extROImpl H kvac crs
  -- (φ*, ρ*) ← A^{Issue, Present, NewUsr, PresentUsr}(pp)
  let challenge := simulateQ oracles (A.run crs pp)
  match ← (challenge.run (cache₂, EXTState.empty kvac crs)).run with
  | .error () => pure true                                    -- Figure 8 `Issue` abort ⇒ win
  | .ok ((φStar, ρStar), cache₃, st) => do
      let (accepts, _) ← runRO H cache₃ (kvac.presentSrv crs sk φStar ρStar)
      let notHonest := decide ((φStar, ρStar) ∉ st.pqrs)
      -- `Ext.P` is `Option`-valued, unlike Figure 8's total `m* := Ext.P(sk, φ*, ρ*)`.
      -- A `none` is an extraction failure: the extractor could not open a presentation
      -- that nonetheless verifies. We read it as satisfying the last disjunct
      -- `(m* ∉ Qrs ∨ φ*(m*) = 0)`, an adversary win, on the same footing as the `Ext.I`
      -- abort in `Issue`. A verifying presentation the extractor cannot open is the
      -- strongest form of the winning event.
      let freshOrUnsat :=
        match ext.extP sk φStar ρStar with
        | none       => true
        | some mStar => decide (mStar ∉ st.qrs) || !kvac.holds crs φStar mStar
      pure (accepts && notHonest && freshOrUnsat)

/-- The extraction advantage of `A` with respect to extractor `ext`: the
probability that `EXTGame` returns `true`. This is `Adv^ext_{KVAC,Ext,A}` of O24
Definition 4.5, the quantity `Extractable` asks to be negligible. An `abbrev`, so
it unfolds in the Theorem 5.2 reduction. -/
noncomputable abbrev EXTAdv (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (ext : Extractor kvac) (A : EXTAdversary H kvac) (secParam n : Nat) : ℝ≥0∞ :=
  Pr[= true | EXTGame H kvac ext A secParam n]

/-! ## Extractability (O24 Definition 4.5) -/

/-- The extraction game as an asymptotic `SecurityGame` for a fixed attribute
count `n` and extractor `ext`: the advantage `Adv^ext` as a function of the
adversary and the security parameter. -/
noncomputable def extSecurityGame (H : HashSpec)
    (kvac : KVACSyntax (OracleComp (ZKRO H))) (ext : Extractor kvac) (n : Nat) :
    SecurityGame (EXTAdversary H kvac) where
  advantage A secParam := EXTAdv H kvac ext A secParam n

/-- Extractability, O24 Definition 4.5: there is an extractor `Ext = (Ext.I, Ext.P)`
such that the extraction game is secure against the efficient adversaries, that is,
`Adv^ext_{KVAC,Ext,A}` is negligible in the security parameter for every p.p.t. `A`.

Unfolding `SecurityGame.secureAgainst`, this reads

  `∃ ext, ∀ A, isPPT A → negligible (fun secParam => EXTAdv H kvac ext A secParam n)`,

which matches the paper's quantifier structure. `∃ ext` is "there exists
`Ext = (Ext.I, Ext.P)`", the `∀ A` is "for any adversary `A`", the `isPPT A →`
guard renders the adjective "p.p.t." (a restricted quantifier, since there is no
type of efficient adversaries to range over), and `negligible (… EXTAdv …)` is
"`Adv^ext` is negligible in λ".

The efficiency predicate `isPPT` is an abstract parameter, exactly as VCVio's
`SecurityGame.secureAgainst` leaves it, because this development fixes no concrete
efficiency notion, that is, no probabilistic-polynomial-time bound (such as a
`PolyQueries` query-count bound), on `OracleComp` adversaries. Taking it as a
parameter renders the paper's "for any p.p.t. A" faithfully, and a concrete
instantiation supplies the efficiency notion. -/
def Extractable (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (isPPT : EXTAdversary H kvac → Prop) (n : Nat) : Prop :=
  ∃ ext : Extractor kvac, (extSecurityGame H kvac ext n).secureAgainst isPPT

/-! ## The `n ≤ poly(λ)` side condition (O24 Definition 4.5) -/

/-- The attribute count `n(λ)`, taken as a function of the security parameter `λ`,
is polynomially bounded: `n λ ≤ c · λ^d + c` for some constants `c, d`. This makes
O24's side condition `n ≤ poly(λ)` an explicit predicate, rather than leaving `n` a
free `Nat` independent of `λ`. -/
def PolyBounded (n : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ lam : ℕ, n lam ≤ c * lam ^ d + c

/-- Asymptotic extractability with O24's `n ≤ poly(λ)` side condition made a proof
obligation. Here the attribute count `n(λ)` is a function of the security parameter;
for every polynomially-bounded `n` there is an extractor making the extraction game,
run at attribute count `n secParam` for each `secParam`, secure against the efficient
adversaries. The `PolyBounded n →` hypothesis is the generated obligation: any proof
of `ExtractablePoly`, or instantiation of it, must exhibit `n`'s polynomial bound
rather than silently assume a constant attribute count. `Extractable` above is the
fixed-`n` slice; this ties `n` to `λ` as the paper does.

The full discharge (a concrete `PolyBounded` witness and the negligibility proof)
belongs to the μCMZ extractability proof, Track CMZ-E (issue #11). -/
def ExtractablePoly (H : HashSpec) (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (isPPT : EXTAdversary H kvac → Prop) : Prop :=
  ∀ n : ℕ → ℕ, PolyBounded n →
    ∃ ext : Extractor kvac,
      (SecurityGame.mk (fun A secParam => EXTAdv H kvac ext A secParam (n secParam))
        : SecurityGame (EXTAdversary H kvac)).secureAgainst isPPT

/-- Obligation generator for O24 Theorem 5.10 (extractability with the `n ≤ poly(λ)`
side condition). Stated over an abstract scheme `kvac` and adversary-efficiency
predicate `isPPT`; the premises the paper uses — scheme correctness and a
knowledge-sound ZKP supplying straight-line extractors (O24 §5.5) — are not yet
formalized, so they are elided here and this stands as a deferred obligation.

The `sorry` is the point: it turns `ExtractablePoly` from a latent definition into a
real open goal, so `PolyBounded n` and the negligibility of `EXTAdv` become subgoals
that the μCMZ extractability proof must discharge. Full proof (and the missing
premises) belong to Track CMZ-E (issue #11), where the concrete μCMZ `KVACSyntax`
instantiates `kvac`. -/
theorem extractablePoly_obligation (H : HashSpec)
    (kvac : KVACSyntax (OracleComp (ZKRO H)))
    (isPPT : EXTAdversary H kvac → Prop) :
    ExtractablePoly H kvac isPPT := by
  sorry

end KVAC.Framework
