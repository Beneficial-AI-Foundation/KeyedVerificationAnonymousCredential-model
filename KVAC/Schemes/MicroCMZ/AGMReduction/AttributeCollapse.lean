/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

/-!
# The `n → 1` attribute collapse (Claim 5.7)

The general-`n` unforgeability bound (Lemma 5.5) routes through the `n = 1`
case (Lemma 5.4, `agm_ufcmva_le_n1_explicit`) by *collapsing* an `n`-attribute
transcript onto a 1-attribute one: pick a direction `r⃗ : Fin n → F`, embed the
public attribute elements as `Xᵢ = rᵢ • X₁` (so their discrete logarithms
satisfy `xᵢ = rᵢ · x₁`), and translate each algebraic representation over the
`n`-attribute basis to one over the 1-attribute basis whose evaluation agrees.

The paper's reduction `B` (Claim 5.7) fixes `z₁ = 1`, samples `zᵢ` for
`i ∈ [2, n]`, and collapses *messages* to `m₁ + Σᵢ zᵢ mᵢ`. Here the direction
`r⃗` ranges over all `n` coordinates: the `n`-game's first attribute element
(index `0` in `Fin n`) is `r₁ • X₁`, with `X₁` the 1-attribute game's public
element (the paper's `z₁ = 1` is the case `r₁ = 1`). Because the AGM game's
`verify`/`help` queries and forgery are algebraic representations, those are
collapsed too. The message collapse `Σᵢ mᵢ rᵢ` is the wrapper's job.

This file holds the pure algebra of that collapse and the wrapper
built on it.

- The two representation translations: `AGMRepr.collapseRepr` for a single
  represented element (submitted to the Verify and Help oracles, and the forgery) and
  `AGMRepr.linCombCollapse` for the weighted sum `Σᵢ rᵢ • Aᵢ` of represented
  elements (submitted to the Help oracle).
- The wrapper `nTo1Adversary A r`: a 1-attribute adversary that runs the
  `n`-attribute adversary `A` along a fixed direction `r⃗`. It builds the
  `n`-attribute public parameters `(X₀, Xᵣ, fun i => rᵢ • X₁)` from the
  1-attribute ones, answers `A`'s queries through `collapseOracleImpl`, which
  forwards each `n`-attribute query to the 1-attribute game's oracle (messages
  through `collapseMsg`, representations through the two translations),
  and translates the forgery back.
- The 3-DL reduction `microCMZN3DLReduction gen A` for general `n`, with its
  experiment and advantage at base `gen`: the direction `r⃗` is a parameter of
  the wrapper (the adversary's `OracleComp (AGMOracleSpec F G 1)` has no
  sampling oracle), so the reduction samples `r⃗` in `ProbComp` and then runs
  the `n = 1` reduction `microCMZ3DLReduction` on the wrapped adversary.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable {n : ℕ}

/-- Collapse an `n`-attribute algebraic representation onto a 1-attribute one
along a direction `r⃗`: every field is preserved except the attribute
coefficients, which are combined into `Σᵢ rᵢ · ρ.x i` (the single `x₁`
coefficient). The coefficients `uv` for issued MAC codes are carried unchanged, since
the issued MAC codes are the same list in both games. It is built so that, against the
1-attribute basis `(g₀, H, X₀, Xᵣ, fun _ => X₁)`, it evaluates as `ρ` does
against the embedded basis `(g₀, H, X₀, Xᵣ, fun i => r i • X₁)`; that
evaluation bridge is not in this file. -/
def AGMRepr.collapseRepr (r : Fin n → F) (ρ : AGMRepr F n) : AGMRepr F 1 where
  g := ρ.g
  h := ρ.h
  x0 := ρ.x0
  xr := ρ.xr
  x := fun _ => ∑ i, r i * ρ.x i
  uv := ρ.uv

/-- Length of the combined list of coefficients for issued MAC codes in `linCombCollapse`: the
maximum of the per-attribute `uv` list lengths. Beyond this length every
`(ρA i).uv.getD k (0, 0)` is `(0, 0)`, so, in the intended evaluation bridge,
both sides contribute `0` at that position (via `List.getD`'s default). -/
def linCombCollapseUVLen (ρA : Fin n → AGMRepr F n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i => ((ρA i).uv).length

/-- Combined 1-attribute representation of the weighted element
`Σᵢ rᵢ • Aᵢ`, where each `Aᵢ` carries the `n`-attribute representation `ρA i`.
It is built to evaluate, against the 1-attribute basis
`(g₀, H, X₀, Xᵣ, fun _ => X₁)`, to `Σᵢ rᵢ • (ρA i).eval` against the embedded
basis `(g₀, H, X₀, Xᵣ, fun j => rⱼ • X₁)`. The Help oracle that `nTo1Adversary`
simulates collapses an `n`-attribute help query through it, and this evaluation identity
is what the coupling `collapse_oracle_coupling` needs.

The scalar-coefficient fields are the weighted sums; the single attribute
coefficient is `Σᵢ Σⱼ rᵢ·rⱼ·(ρA i).x j` (the collapsed attribute coefficient
of the weighted representation); the coefficients for issued MAC codes combine per position up
to `linCombCollapseUVLen`. -/
def AGMRepr.linCombCollapse (r : Fin n → F) (ρA : Fin n → AGMRepr F n) :
    AGMRepr F 1 where
  g := ∑ i, r i * (ρA i).g
  h := ∑ i, r i * (ρA i).h
  x0 := ∑ i, r i * (ρA i).x0
  xr := ∑ i, r i * (ρA i).xr
  x := fun _ => ∑ i, ∑ j, r i * r j * (ρA i).x j
  uv := (List.range (linCombCollapseUVLen ρA)).map fun k =>
    (∑ i, r i * ((ρA i).uv.getD k (0, 0)).1,
     ∑ i, r i * ((ρA i).uv.getD k (0, 0)).2)

/-! ## The `n → 1` query-translation wrapper -/

/-- The collapsed message `Σᵢ mᵢ · rᵢ` of the `n → 1` wrapper. -/
def collapseMsg (r m : Fin n → F) : Fin 1 → F := fun _ => ∑ i, m i * r i

/-- Query-translation oracle of the `n → 1` collapse. Each `n`-attribute query
becomes one 1-attribute `query` in `OracleComp (AGMOracleSpec F G 1)`: messages
through `collapseMsg`, representations through `AGMRepr.collapseRepr` /
`AGMRepr.linCombCollapse`. Response types (`G × G` / `Bool`) agree in both specs,
so responses pass through.

A `help` query's vector `ρ⃗` collapses to the single representation
`linCombCollapse r ρ⃗`, which the 1-attribute oracle evaluates to the weighted sum
`Σᵢ rᵢ • Aᵢ` of the elements `Aᵢ` that `ρ⃗` represents over the embedded basis
`Xᵢ = rᵢ • X₁`. Its `help` answer `Z = (x₀+xᵣ)•A₀ + x₁•Σᵢ rᵢ•Aᵢ` is then the
`n`-attribute answer at the embedded key `xᵢ = rᵢ·x₁`. -/
noncomputable def collapseOracleImpl (r : Fin n → F) :
    QueryImpl (AGMOracleSpec F G n) (OracleComp (AGMOracleSpec F G 1))
  | .sign m => query (spec := AGMOracleSpec F G 1) (AGMQuery.sign (collapseMsg r m))
  | .verify m ρU ρV => query (spec := AGMOracleSpec F G 1)
      (AGMQuery.verify (collapseMsg r m) (AGMRepr.collapseRepr r ρU)
        (AGMRepr.collapseRepr r ρV))
  | .help ρ₀ ρA ρZ => query (spec := AGMOracleSpec F G 1)
      (AGMQuery.help (AGMRepr.collapseRepr r ρ₀) (fun _ => AGMRepr.linCombCollapse r ρA)
        (AGMRepr.collapseRepr r ρZ))

/-- The `n → 1` attribute-collapse wrapper adversary (Claim 5.7). For a fixed
direction `r⃗`, a 1-attribute adversary that runs `A` on the `n`-attribute public
parameters `(X₀, Xᵣ, fun i => rᵢ • X₁)` against `collapseOracleImpl` and returns
the collapsed forgery. -/
noncomputable def nTo1Adversary (A : AGMUFAdversary F G n) (r : Fin n → F) :
    AGMUFAdversary F G 1 where
  run H pp := do
    let pp_n : G × G × (Fin n → G) := (pp.1, pp.2.1, fun i => r i • pp.2.2 0)
    let (mStar_n, ρU_n, ρV_n) ← simulateQ (collapseOracleImpl r) (A.run H pp_n)
    pure (collapseMsg r mStar_n, AGMRepr.collapseRepr r ρU_n, AGMRepr.collapseRepr r ρV_n)

/-- The 3-DL reduction for general `n` (Claim 5.7 on top of Lemma 5.4): samples
the direction `r⃗ ←$ Fⁿ`, wraps `A` as a 1-attribute adversary, and runs the
`n = 1` reduction `microCMZ3DLReduction` on the wrapper at the challenge powers
`pows`. Like `microCMZ3DLReduction` it takes the powers alone and is sound only
at base `gen`; the `QDLogAdversary` shape is formed once, in
`microCMZN3DLReductionExp`, always at `gen`. -/
noncomputable def microCMZN3DLReduction (A : AGMUFAdversary F G n) (pows : Fin 3 → G) :
    ProbComp F := do
  let r ← $ᵗ (Fin n → F)
  microCMZ3DLReduction gen (nTo1Adversary A r) pows

/-- The 3-DL experiment for the general-`n` reduction, the counterpart of
`microCMZ3DLReductionExp`: the challenge base is fixed to `gen` and the base slot
`qdlogExp` passes is discarded. -/
noncomputable def microCMZN3DLReductionExp (A : AGMUFAdversary F G n) : ProbComp Bool :=
  qdlogExp 3 gen (fun _g pows => microCMZN3DLReduction gen A pows)

/-- The 3-DL advantage of the general-`n` reduction at base `gen`, the 3-DL term
of Lemma 5.5's bound. -/
noncomputable abbrev microCMZN3DLReductionAdv (A : AGMUFAdversary F G n) : ℝ≥0∞ :=
  Pr[= true | microCMZN3DLReductionExp gen A]

end KVAC.Schemes.MicroCMZ
