/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.AGMReduction.GapDLReduction

/-!
# The gap-DL reduction of the collision case of Theorem 5.11 (O24 §5.6)

The general-`n` bound of O24 Theorem 5.11 (p. 46) splits the winning event on
whether the forgeries' attribute combinations `Σᵢ mᵢ•Xᵢ` are pairwise distinct. The
colliding case is reduced to gap-DL "using an argument similar to Theorem 5.5",
the paper's text citing its Lemma 5.5. This file gives that reduction,
`omufGapDLReduction`, on the pattern of `gapDlReduction` (Claim 5.6,
`AGMReduction/GapDLReduction.lean`), and reuses its embedding of the challenge.

## The embedding

The reduction holds the challenge `X = x•g` and the DDH-decision oracle. It
samples masks `aaᵢ, bbᵢ`, `z`, `xᵣ` and the crs `H ←$ G×`, and runs the forger on
`(H, (z•H, xᵣ•g, aaᵢ•g + bbᵢ•X))`, so that the implicit key is `xᵢ = aaᵢ + bbᵢ·x`,
`x₀ = z`, with `xᵣ` known. `omufGapDlOracleImpl` answers the forger's oracles:

- `sign C' ρ` runs the gate on known group elements. On a match it answers with
  `U' = u•g`, `V' = z•U' + u•(C' + xᵣ•g)` for a nonzero `u`, which needs no
  secret beyond `z` and `xᵣ`: in this game the blind issuance never touches the
  attribute keys `xᵢ`, only the commitment `C'` the forger supplies. A mismatch
  is refused and logged, as in `agmOMUFOracleImpl`.
- `verify m⃗ σ ρU ρV` checks both gates and `σ.1 ≠ 0` on known elements, and
  decides `σ.2 = (c + x·d)•σ.1` with the one DDH query `Ddh(d•σ.1, σ.2 − c•σ.1)`
  (`(c, d) = gapDlKeyParts`).
- a coin query is forwarded to the reduction's own `unifSpec`, leaving the log
  untouched.

## The extraction

`OMUFWins` makes the forgeries' attribute vectors pairwise distinct
(`(out.map Prod.fst).Nodup`), so two forgeries whose combinations agree,
`Σᵢ m*ᵢ•Xᵢ = Σᵢ mⱼ,ᵢ•Xᵢ`, have `m⃗* ≠ m⃗ⱼ`, and the relation
`(Σᵢ (m*ᵢ − mⱼ,ᵢ)·aaᵢ)•g = −(Σᵢ (m*ᵢ − mⱼ,ᵢ)·bbᵢ)•X` gives
`x = (Σᵢ aaᵢ·(m*ᵢ − mⱼ,ᵢ)) · (Σᵢ bbᵢ·(mⱼ,ᵢ − m*ᵢ))⁻¹`, as in `gapDlReduction`. The pair
is found by recomputation, no DDH query. The bad event
`Σᵢ bbᵢ·(mⱼ,ᵢ − m*ᵢ) = 0` is degree one in the perfectly hidden `bbᵢ`; the
reduction then outputs `0`, as it does without a colliding pair. The comparison
of the reduction's view with the game's, and the `1/p` loss, are the proof's.

Unlike `gapDlReduction`, the colliding pair is between two forgeries, not
between a forgery and a signed message, since the one-more forger signs through
commitments, not attribute vectors.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable {n : ℕ}

/-- **Oracle simulator of the collision-case reduction** (O24 Theorem 5.11). Answers
the forger's Sign and Verify queries under the embedding `gapDlEmbedParams`, with
the log of `agmOMUFOracleImpl`. See the module docstring for the arms. -/
noncomputable def omufGapDlOracleImpl (aa bb : Fin n → F) (z xr : F) (X H : G) :
    QueryImpl (AGMOMUFOracleSpec F G n)
      (StateT (AGMOMUFLog F G n) (OracleComp (unifSpec + GapDLogOracleSpec G)))
  | .sign C' ρ => StateT.mk fun log => do
      let pp := gapDlEmbedParams gen aa bb z xr X H
      if reprMatches ρ gen H pp.1 pp.2.1 pp.2.2 (AGMOMUFLog.tags log) C' then do
        let u ← (gapSignScalarSample : OracleComp (unifSpec + GapDLogOracleSpec G) F)
        let U := u • gen
        let V := z • U + u • (C' + xr • gen)
        pure (some (U, V), log ++ [(C', ρ, some (U, V))])
      else
        pure (none, log ++ [(C', ρ, none)])
  | .verify m σ ρU ρV => StateT.mk fun log => do
      let tags := AGMOMUFLog.tags log
      let pp := gapDlEmbedParams gen aa bb z xr X H
      let consistent :=
        reprMatches ρU gen H pp.1 pp.2.1 pp.2.2 tags σ.1 ∧
        reprMatches ρV gen H pp.1 pp.2.1 pp.2.2 tags σ.2
      let (c, d) := gapDlKeyParts aa bb z xr m
      let bit ← query (spec := unifSpec + GapDLogOracleSpec G)
        (Sum.inr (d • σ.1, σ.2 - c • σ.1))
      pure (decide consistent && decide (σ.1 ≠ 0) && bit, log)

/-- The first pair of forgeries with different attribute vectors and equal
attribute combination `Σᵢ mᵢ•Xᵢ` over the bases `Xv`, if any. -/
def collidingForgeries (Xv : Fin n → G) (out : List (AGMOMUFForgery F G n)) :
    Option (AGMOMUFForgery F G n × AGMOMUFForgery F G n) :=
  (out.flatMap fun e => out.map fun e' => (e, e')).find? fun p =>
    decide (p.1.msg ≠ p.2.msg ∧ (∑ i, p.1.msg i • Xv i) = ∑ i, p.2.msg i • Xv i)

/--
The gap-DL reduction of the collision case of O24 Theorem 5.11 at general `n`
(p. 46, two forgeries with equal attribute combination `Σᵢ mᵢ·Xᵢ`, "reduced to
DL using an argument similar to Theorem 5.5", the paper's text citing its
Lemma 5.5 as a theorem), built from an `n`-attribute algebraic one-more
forger. It embeds the challenge `X = x•g` as `Xᵢ = aaᵢ•g + bbᵢ•X`, simulates the
forger through `omufGapDlOracleImpl`, and on a colliding pair of forgeries
returns `x = (Σᵢ aaᵢ·(m*ᵢ − mⱼ,ᵢ)) · (Σᵢ bbᵢ·(mⱼ,ᵢ − m*ᵢ))⁻¹`, and `0` when there is
none or the denominator vanishes (`0⁻¹ = 0`). It randomises freely, since
`GapDLogAdversary` has an oracle for uniform sampling. The base slot of the
gap-DL experiment is discarded and `gen` used, so the reduction is sound only at
base `gen`, as `gapDlReduction`. The crs `H` is drawn from the nonzero elements,
as `setup` does.
-/
noncomputable def omufGapDLReduction {n : ℕ} (gen : G) (A : AGMOMUFAdversary F G n) :
    GapDLogAdversary F G :=
  fun _ X => do
    let aa ← ($ᵗ (Fin n → F) : OracleComp (unifSpec + GapDLogOracleSpec G) (Fin n → F))
    let bb ← ($ᵗ (Fin n → F) : OracleComp (unifSpec + GapDLogOracleSpec G) (Fin n → F))
    let z ← ($ᵗ F : OracleComp (unifSpec + GapDLogOracleSpec G) F)
    let xr ← ($ᵗ F : OracleComp (unifSpec + GapDLogOracleSpec G) F)
    let H ← (uniformNonzero G : OracleComp (unifSpec + GapDLogOracleSpec G) G)
    let pp := gapDlEmbedParams gen aa bb z xr X H
    -- `HAdd.hAdd` rather than `+`, as in `AGM_OMUFGame`.
    let impl := HAdd.hAdd
      ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + GapDLogOracleSpec G))).liftTarget
        (StateT (AGMOMUFLog F G n) (OracleComp (unifSpec + GapDLogOracleSpec G))))
      (omufGapDlOracleImpl gen aa bb z xr X H)
    let (out, _) ← (simulateQ impl (A.run H pp)).run []
    match collidingForgeries pp.2.2 out with
    | some (e, e') =>
        let num := ∑ i, aa i * (e.msg i - e'.msg i)
        let den := ∑ i, bb i * (e'.msg i - e.msg i)
        pure (num * den⁻¹)
    | none => pure 0

end KVAC.Schemes.MicroCMZ
