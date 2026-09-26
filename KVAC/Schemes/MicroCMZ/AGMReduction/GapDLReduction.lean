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

The implicit secret key is `xᵢ = aaᵢ + bbᵢ·x` for self-sampled masks `aaᵢ, bbᵢ`,
so `Xᵢ = aaᵢ•g + bbᵢ•X`; `x₀ = z` (so `X₀ = z•H`) and `xᵣ` are honestly known
(`gapDlEmbedParams`). On a message `m⃗` the game's key `x₀ + xᵣ + Σᵢ mᵢxᵢ` is
`c + x·d` with `c`, `d` computed from the masks alone (`gapDlKeyParts`). `sign`
uses a nonzero scalar `u` and `U = u•g`, for which `x·d•U = u•(d•X)` is known, so
`V = c•U + u•(d•X) = key•U`; `verify` and `help` run the honest
representation-consistency check on known group elements and decide the one
`x`-dependent equation with a single DDH query. The verify and help bits equal
the honest game's; the sign answer has the honest law once `g` is a generator
(the bijectivity `Fact` the proof leaf assumes), since `u ↦ u•g` then carries
the nonzero-scalar sampler onto the honest `U ←$ G∖{0}`.

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

/-! ## The embedded parameters -/

/-- **Nonzero-scalar sampler for the simulator's `sign` arm.** Definitionally
`uniformUnits F` (`Construction.lean`), kept as a named `@[irreducible]`
definition, like `reductionMaskSample`, so the proof leaf reasons about the
`sign` branch through named distribution lemmas instead of unfolding the sampler.
Never write `$ᵗ {u : F // u ≠ 0}` at a use site: that subtype-`SampleableType`
search loops. -/
@[irreducible] noncomputable def gapSignScalarSample : ProbComp F := uniformUnits F

/-- The embedded public parameters `(X₀, Xᵣ, X⃗) = (z•H, xᵣ•g, aaᵢ•g + bbᵢ•X)`,
in the `(X₀, Xᵣ, X⃗)` shape of `agmOracleImpl`'s `pp`. -/
noncomputable def gapDlEmbedParams (aa bb : Fin n → F) (z xr : F) (X H : G) :
    G × G × (Fin n → G) :=
  (z • H, xr • gen, fun i => aa i • gen + bb i • X)

/-- The game's key on `m⃗` split as `c + x·d`: `c = z + xᵣ + Σᵢ aaᵢ·mᵢ` and
`d = Σᵢ bbᵢ·mᵢ`, both computable from the masks alone. -/
def gapDlKeyParts (aa bb : Fin n → F) (z xr : F) (m : Fin n → F) : F × F :=
  (z + xr + ∑ i, aa i * m i, ∑ i, bb i * m i)

/-! ## The gap-DL oracle simulator -/

/-- **Type-(i) oracle simulator (Claim 5.6).** Answers the μCMZ AGM oracles
for an adversary that knows only the embedded public parameters, using the gap-DL
DDH-decision oracle to decide the key-dependent `Verify`/`Help` equations without
knowing the challenge exponent `x` (where `X = x·g`, `g = gen`).

The *implicit* secret key is embedded as `xᵢ = aaᵢ + bbᵢ·x` (so `Xᵢ = aaᵢ·g +
bbᵢ·X`), `x₀ = z` (so `X₀ = z·H`), and `xᵣ` honestly known (so `Xᵣ = xᵣ·g`):
`pp = gapDlEmbedParams`. Writing `(c, d) = gapDlKeyParts` for `c := z + xᵣ +
Σᵢ aaᵢ·mᵢ` and `d := Σᵢ bbᵢ·mᵢ`, the game's key on message `m⃗` is
`key = (x₀+xᵣ+Σᵢ mᵢ·xᵢ) = c + x·d`. Each arm reproduces `agmOracleImpl`'s
behaviour under this embedding (the representation-consistency check `consistent`
is a pure function of the *known* group elements `g, H, pp` and the logged tags,
so the reduction computes it directly):

- `.sign m⃗`: sample `u ← gapSignScalarSample` (nonzero), set `U := u·g`; then
  `key·U = c·U + u·(d·X)` (since `x·d·U = u·d·X`), so `V := c·U + u·(d·X)`;
  append `(m⃗, (U,V))` to the log.
- `.verify m⃗ σ ρU ρV`: check `consistent` and `σ.1 ≠ 0`; the honest bit
  `σ.2 = key·σ.1 = c·σ.1 + x·(d·σ.1)` is decided by `Ddh(d·σ.1, σ.2 − c·σ.1)`
  (which returns `1 ⟺ σ.2 − c·σ.1 = x·(d·σ.1)`). The paper's `Σᵢ bᵢmᵢ = 0`
  branch is subsumed: `gapDdhOracleImpl` is total and `Ddh(0, w) = decide (w = 0)`,
  the same bit as `σ.2 = c·σ.1`. The query is issued even when `consistent`
  fails or `σ.1 = 0`; no bound here counts DDH queries.
- `.help A₀ A⃗ Z ρ₀ ρA ρZ`: check `helpConsistent`; the honest bit
  `Z = (x₀+xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ = (z+xᵣ)·A₀ + Σᵢ aaᵢ·Aᵢ + x·(Σᵢ bbᵢ·Aᵢ)` via
  `Ddh(Σᵢ bbᵢ·Aᵢ, Z − (z+xᵣ)·A₀ − Σᵢ aaᵢ·Aᵢ)`.

Verify and help are bit-exact (the DDH bit equals the honest game bit). Sign is
exact in law once `g` is a generator (the bijectivity `Fact` the proof leaf
assumes): `u ↦ u·g` carries the scalar sampler onto the honest `U ←$ G∖{0}` and
`V = key·U`; the proof leaf couples the two samplers along that bijection. The
paper (Claim 5.6) folds `xᵣ` into `z` and prints the `Ddh` arguments without
the `Σᵢ aaᵢ·mᵢ` / `xᵣ` terms; those are typos, corrected here to be faithful to
this game's `Xᵣ` term. -/
noncomputable def gapDlOracleImpl (aa bb : Fin n → F) (z xr : F) (X H : G) :
    QueryImpl (AGMOracleSpec F G n)
      (StateT (AGMLog F G n) (OracleComp (unifSpec + GapDLogOracleSpec G)))
  | .sign m => StateT.mk fun log => do
      let u ← (gapSignScalarSample : OracleComp (unifSpec + GapDLogOracleSpec G) F)
      let U := u • gen
      let (c, d) := gapDlKeyParts aa bb z xr m
      let V := c • U + u • (d • X)
      pure ((U, V), log ++ [(m, (U, V))])
  | .verify m σ ρU ρV => StateT.mk fun log => do
      let tags := log.map Prod.snd
      let pp := gapDlEmbedParams gen aa bb z xr X H
      let consistent :=
        ρU.eval gen H pp.1 pp.2.1 pp.2.2 tags = σ.1 ∧
        ρV.eval gen H pp.1 pp.2.1 pp.2.2 tags = σ.2
      let (c, d) := gapDlKeyParts aa bb z xr m
      let bit ← query (spec := unifSpec + GapDLogOracleSpec G)
        (Sum.inr (d • σ.1, σ.2 - c • σ.1))
      pure (decide consistent && decide (σ.1 ≠ 0) && bit, log)
  | .help A₀ A Z ρ₀ ρA ρZ => StateT.mk fun log => do
      let tags := log.map Prod.snd
      let pp := gapDlEmbedParams gen aa bb z xr X H
      let consistent := helpConsistent gen H pp tags A₀ A Z ρ₀ ρA ρZ
      let bit ← query (spec := unifSpec + GapDLogOracleSpec G)
        (Sum.inr (∑ i, bb i • A i, Z - (z + xr) • A₀ - ∑ i, aa i • A i))
      pure (decide consistent && bit, log)

end KVAC.Schemes.MicroCMZ
