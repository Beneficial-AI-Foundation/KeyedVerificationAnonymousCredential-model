/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AlgebraicMAC

/-!
# The gap-DL oracle simulator (Claim 5.6)

The general-`n` unforgeability bound (Lemma 5.5) splits a winning forgery on
whether its attribute combination `Σᵢ m*ᵢ•Xᵢ` collides with that of a signed
message. The colliding case (Claim 5.6) is bounded by the gap discrete-log
advantage: a reduction holding the challenge `X = x•g` and the DDH-decision
oracle embeds `x` into the public parameters and runs the adversary. This file
provides the simulator that answers the adversary's AGM oracles under that
embedding; the reduction around it (masks, `crs`, extraction) extends this file.

The implicit secret key is `xᵢ = aᵢ + bᵢ·x` for self-sampled masks `aᵢ, bᵢ`, so
`Xᵢ = aᵢ•g + bᵢ•X`; `x₀ = z` (so `X₀ = z•H`) and `xᵣ` are honestly known. On a
message `m⃗` the game's key `x₀ + xᵣ + Σᵢ mᵢxᵢ` is `c + x·d` with `c`, `d` computed
from the masks alone. `sign` uses a nonzero scalar `u` and `U = u•g`, for which
`x·d•U = u•(d•X)` is known; `verify` and `help` run the honest
representation-consistency check on known group elements and decide the one
`x`-dependent equation with a single DDH query. The verify and help answers
equal the honest game's; only the law of `U` differs from the honest
`U ←$ {g // g ≠ 0}`.

**Sampling landmine.** The automatic `SampleableType {u : F // u ≠ 0}` instance
search loops, so the sampler is built explicitly (`instSampleableNonzeroScalar`)
and wrapped in the irreducible `gapSignScalarSample`; the instance must be
declared before the sampler.

This file imports only `AlgebraicMAC`, so the later `• gen`-algebra proofs about
the simulator can live in a leaf free of `AGMPolynomial`'s instance context.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable {n : ℕ}

/-- Explicit `SampleableType {u : F // u ≠ 0}` for nonzero-scalar sampling
(`gapSignScalarSample` below). The *automatic* subtype-`SampleableType` search
loops, so the instance is built explicitly through `SampleableType.ofNonemptySubtype`,
nonempty via `1`. -/
noncomputable instance instSampleableNonzeroScalar :
    SampleableType {u : F // u ≠ 0} :=
  SampleableType.ofNonemptySubtype (fun u : F => u ≠ 0) ⟨⟨1, one_ne_zero⟩⟩

/-- **Opaque nonzero-scalar sampler for the gap-DL simulator's `sign` arm.**
Definitionally `$ᵗ {u : F // u ≠ 0}` (using the explicit `instSampleableNonzeroScalar`),
kept as a named `@[irreducible]` definition so the `MvPolynomial`-heavy proof context
reasons about the `sign` branch through named distribution lemmas without unfolding
the raw `$ᵗ`. -/
@[irreducible] noncomputable def gapSignScalarSample :
    ProbComp {u : F // u ≠ 0} :=
  ($ᵗ {u : F // u ≠ 0} : ProbComp {u : F // u ≠ 0})

/-! ## The gap-DL oracle simulator -/

/-- **Type-(i) oracle simulator (Claim 5.6).** Answers the μCMZ AGM oracles
for an adversary that knows only the embedded public parameters, using the gap-DL
DDH-decision oracle to decide the key-dependent `Verify`/`Help` equations without
knowing the challenge exponent `x` (where `X = x·g`, `g = gen`).

The *implicit* secret key is embedded as `xᵢ = aaᵢ + bbᵢ·x` (so `Xᵢ = aaᵢ·g +
bbᵢ·X`), `x₀ = z` (so `X₀ = z·H`), and `xᵣ` honestly known (so `Xᵣ = xᵣ·g`).
Writing `c := z + xᵣ + Σᵢ aaᵢ·mᵢ` and `d := Σᵢ bbᵢ·mᵢ`, the game's key on message
`m⃗` is `key = (x₀+xᵣ+Σᵢ mᵢ·xᵢ) = c + x·d`. Each arm reproduces `agmOracleImpl`'s
behaviour under this embedding (the representation-consistency check `consistent`
is a pure function of the *known* group elements `g, H, X₀, Xᵣ, X⃗` and the logged
tags, so the reduction computes it directly):

- `.sign m⃗`: sample `u ←$ F`, set `U := u·g`; then `key·U = c·U + u·(d·X)` (since
  `x·d·U = u·d·X`), so `V := c·U + u·(d·X)`; append `(m⃗, (U,V))` to the log.
- `.verify m⃗ σ ρU ρV`: check `consistent` and `σ.1 ≠ 0`; the honest bit
  `σ.2 = key·σ.1 = c·σ.1 + x·(d·σ.1)` is decided directly when `d = 0`, else via
  `Ddh(d·σ.1, σ.2 − c·σ.1)` (which returns `1 ⟺ σ.2 − c·σ.1 = x·(d·σ.1)`).
- `.help A₀ A⃗ Z ρ₀ ρA ρZ`: check `consistent`; the honest bit
  `Z = (x₀+xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ = (z+xᵣ)·A₀ + Σᵢ aaᵢ·Aᵢ + x·(Σᵢ bbᵢ·Aᵢ)` via
  `Ddh(Σᵢ bbᵢ·Aᵢ, Z − (z+xᵣ)·A₀ − Σᵢ aaᵢ·Aᵢ)`.

Verify/Help are *exact* (the DDH bit equals the honest game bit); the only
distributional gap is the `.sign` `U`-law (`u ←$ F` here vs `U ←$ {g // g ≠ 0}`
in `mac`), reconciled by the proof of the collision-case bound. The
paper (O24 Claim 5.6) folds `xᵣ` into `z` and prints the `Ddh` arguments without
the `Σᵢ aaᵢ·mᵢ` / `xᵣ` terms; those are typos, corrected here to be faithful to
this game's `Xᵣ` term. -/
noncomputable def gapDlOracleImpl (aa bb : Fin n → F) (z xr : F) (X H : G) :
    QueryImpl (AGMOracleSpec F G n)
      (StateT (AGMLog F G n) (OracleComp (unifSpec + GapDLogOracleSpec G)))
  | .sign m => StateT.mk fun log => do
      let u ← (gapSignScalarSample :
        OracleComp (unifSpec + GapDLogOracleSpec G) {u : F // u ≠ 0})
      let U := u.val • gen
      let c := z + xr + ∑ i, aa i * m i
      let d := ∑ i, bb i * m i
      let V := c • U + u.val • (d • X)
      pure ((U, V), log ++ [(m, (U, V))])
  | .verify m σ ρU ρV => StateT.mk fun log => do
      let tags := log.map Prod.snd
      let X0 := z • H
      let Xr := xr • gen
      let Xv := fun i => aa i • gen + bb i • X
      let consistent :=
        ρU.eval (gen) H X0 Xr Xv tags = σ.1 ∧
        ρV.eval (gen) H X0 Xr Xv tags = σ.2
      let c := z + xr + ∑ i, aa i * m i
      let d := ∑ i, bb i * m i
      if d = 0 then
        pure (decide consistent && decide (σ.1 ≠ 0) && decide (σ.2 = c • σ.1), log)
      else
        let bit ← query (spec := unifSpec + GapDLogOracleSpec G)
          (Sum.inr (d • σ.1, σ.2 - c • σ.1))
        pure (decide consistent && decide (σ.1 ≠ 0) && bit, log)
  | .help A₀ A Z ρ₀ ρA ρZ => StateT.mk fun log => do
      let tags := log.map Prod.snd
      let X0 := z • H
      let Xr := xr • gen
      let Xv := fun i => aa i • gen + bb i • X
      let consistent :=
        ρ₀.eval (gen) H X0 Xr Xv tags = A₀ ∧
        (∀ i, (ρA i).eval (gen) H X0 Xr Xv tags = A i) ∧
        ρZ.eval (gen) H X0 Xr Xv tags = Z
      let bit ← query (spec := unifSpec + GapDLogOracleSpec G)
        (Sum.inr (∑ i, bb i • A i, Z - (z + xr) • A₀ - ∑ i, aa i • A i))
      pure (decide consistent && bit, log)

end KVAC.Schemes.MicroCMZ
