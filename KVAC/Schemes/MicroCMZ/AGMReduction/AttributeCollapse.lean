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
element (the paper's `z₁ = 1` is the case `r₁ = 1`). Because the instrumented
game's `verify`/`help` queries carry algebraic representations, those are
collapsed too. The message collapse `Σᵢ mᵢ rᵢ` is the wrapper's job.

This file holds the pure algebra of that collapse and the wrapper
built on it.

- The two representation translations: `AGMRepr.collapseRepr` for a single
  represented element (the `verify`/`help` arms and the forgery) and
  `AGMRepr.linCombCollapse` for the weighted sum `Σᵢ rᵢ • Aᵢ` of represented
  elements (the `help` arm).
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
coefficient). Tag coefficients `uv` are carried unchanged, since the issued
tags are the same list in both games. It is built so that, against the
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

/-- Length of the combined tag-coefficient list for `linCombCollapse`: the
maximum of the per-attribute `uv` list lengths. Beyond this length every
`(ρA i).uv.getD k (0, 0)` is `(0, 0)`, so, in the intended evaluation bridge,
both sides contribute `0` to that tag position (via `List.getD`'s default). -/
def linCombCollapseUVLen (ρA : Fin n → AGMRepr F n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i => ((ρA i).uv).length

/-- Combined 1-attribute representation of the weighted element
`Σᵢ rᵢ • Aᵢ`, where each `Aᵢ` carries the `n`-attribute representation `ρA i`.
It is built to evaluate, against the 1-attribute basis
`(g₀, H, X₀, Xᵣ, fun _ => X₁)`, to `Σᵢ rᵢ • (ρA i).eval` against the embedded
basis `(g₀, H, X₀, Xᵣ, fun j => rⱼ • X₁)`. The `help` arm of `nTo1Adversary`
collapses an `n`-attribute help query through it, and this evaluation identity
is what the coupling `collapse_oracle_coupling` needs.

The scalar-coefficient fields are the weighted sums; the single attribute
coefficient is `Σᵢ Σⱼ rᵢ·rⱼ·(ρA i).x j` (the collapsed attribute coefficient
of the weighted representation); the tag coefficients combine per position up
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
`AGMRepr.linCombCollapse`, and the `help` query's `A⃗` field to `Σᵢ rᵢ • Aᵢ`.
Response types (`G × G` / `Bool`) agree in both specs, so responses pass through.

On a `help` query the oracle first checks the honest `n`-attribute representation
consistency `helpConsistent` (`∀ i, (ρA i).eval = Aᵢ`, plus `ρ₀`, `ρZ`) against
the embedded `n`-attribute basis, and forwards the collapsed 1-attribute `help`
query only if it holds; otherwise it answers `false`, as the honest `n`-attribute
oracle does. The check is needed because the honest `help` check is per attribute
(`∀ i`), while `linCombCollapse` only lets the 1-attribute oracle re-check the
`r`-weighted *sum* `Σᵢ rᵢ·(ρA i).eval = Σᵢ rᵢ·Aᵢ`, which is strictly weaker for
`n ≥ 2` (individually wrong representations whose weighted errors cancel). A
genuine algebraic adversary never trips it (its `Aᵢ = (ρA i).eval`). The
pre-check is what lets the `sign`/`verify`/`help` answers be coupled exactly with
the embedded-key `n`-attribute oracle; that coupling is the blueprint stub
`collapse_oracle_coupling`, not in this file.

The oracle tracks the issued-tag list `List (G × G)` as its state (each forwarded
`sign` appends the returned tag) so that the `help` consistency `eval` uses the
same transcript the honest oracle would. The closed-over `(H, pp_n)` is the
embedded `n`-attribute basis `(H, X₀, Xᵣ, X⃗)`. -/
noncomputable def collapseOracleImpl (r : Fin n → F) (H : G)
    (pp_n : G × G × (Fin n → G)) :
    QueryImpl (AGMOracleSpec F G n)
      (StateT (List (G × G)) (OracleComp (AGMOracleSpec F G 1)))
  | .sign m => StateT.mk fun tags => do
      let σ : G × G ← query (spec := AGMOracleSpec F G 1)
        (AGMQuery.sign (collapseMsg r m))
      pure (σ, tags ++ [σ])
  | .verify m σ ρU ρV => StateT.mk fun tags => do
      let b ← query (spec := AGMOracleSpec F G 1)
        (AGMQuery.verify (collapseMsg r m) σ
          (AGMRepr.collapseRepr r ρU) (AGMRepr.collapseRepr r ρV))
      pure (b, tags)
  | .help A₀ A Z ρ₀ ρA ρZ => StateT.mk fun tags => do
      let consistent := helpConsistent gen H pp_n tags A₀ A Z ρ₀ ρA ρZ
      if consistent then do
        let b ← query (spec := AGMOracleSpec F G 1)
          (AGMQuery.help A₀ (fun _ => ∑ i, r i • A i) Z
            (AGMRepr.collapseRepr r ρ₀) (fun _ => AGMRepr.linCombCollapse r ρA)
            (AGMRepr.collapseRepr r ρZ))
        pure (b, tags)
      else
        pure (false, tags)

/-- The `n → 1` attribute-collapse wrapper adversary (Claim 5.7). For a fixed
direction `r⃗`, a 1-attribute adversary that runs `A` against
`collapseOracleImpl` and returns the collapsed forgery. The tag-tracking state
starts empty and is projected away (`StateT.run' []`). -/
noncomputable def nTo1Adversary (A : AGMUFAdversary F G n) (r : Fin n → F) :
    AGMUFAdversary F G 1 where
  run H pp := do
    let pp_n : G × G × (Fin n → G) := (pp.1, pp.2.1, fun i => r i • pp.2.2 0)
    let (mStar_n, σStar, ρU_n, ρV_n) ←
      (simulateQ (collapseOracleImpl gen r H pp_n) (A.run H pp_n)).run' []
    pure (collapseMsg r mStar_n, σStar,
      AGMRepr.collapseRepr r ρU_n, AGMRepr.collapseRepr r ρV_n)

/-- The 3-DL reduction for general `n` (Claim 5.7 on top of Lemma 5.4): samples
the direction `r⃗ ←$ Fⁿ`, wraps `A` as a 1-attribute adversary, and runs the
`n = 1` reduction `microCMZ3DLReduction` on the wrapper at the challenge powers
`pows`. Like `microCMZ3DLReduction` it takes the powers alone and is sound only
at base `gen`; the `QDLogAdversary` shape is formed once, in
`microCMZN3DLReductionExp`, always at `gen`. -/
noncomputable def microCMZN3DLReduction (A : AGMUFAdversary F G n) (pows : Fin 3 → G) :
    ProbComp F := do
  let r ← $ᵗ (Fin n → F)
  microCMZ3DLReduction gen (nTo1Adversary gen A r) pows

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
