/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AlgebraicMAC

/-!
# The `n → 1` attribute collapse (O24 Claim 5.7)

The general-`n` unforgeability bound (O24 Lemma 5.5) routes through the `n = 1`
case (Lemma 5.4, `agm_ufcmva_le_n1_explicit`) by *collapsing* an `n`-attribute
transcript onto a 1-attribute one: pick a direction `r⃗ : Fin n → F`, embed the
public attribute elements as `Xᵢ = rᵢ • X₁` (so their discrete logarithms
satisfy `xᵢ = rᵢ · x₁`), and translate each algebraic representation over the
`n`-attribute basis to one over the 1-attribute basis whose evaluation agrees.

This file holds the pure-algebra dictionary of that collapse: the two
representation translations, `AGMRepr.collapseRepr` for a single represented
element (the `sign`/`verify` arms and the forgery) and `AGMRepr.linCombCollapse`
for the weighted sum `Σᵢ rᵢ • Aᵢ` of represented elements (the `help` arm).
The wrapper adversary built on them, and the evaluation bridges that justify
the translations, are added on top of this dictionary.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

variable {F : Type} [Field F]
variable {n : ℕ}

/-- Collapse an `n`-attribute algebraic representation onto a 1-attribute one
along a direction `r⃗`: every field is preserved except the attribute
coefficients, which are combined into `Σᵢ rᵢ · ρ.x i` (the single `x₁`
coefficient). Tag coefficients `uv` are carried unchanged, since the issued
tags are the same list in both games. Against the 1-attribute basis
`(g₀, H, X₀, Xᵣ, fun _ => X₁)` it evaluates as `ρ` does against the embedded
basis `(g₀, H, X₀, Xᵣ, fun i => r i • X₁)`. -/
def AGMRepr.collapseRepr (r : Fin n → F) (ρ : AGMRepr F n) : AGMRepr F 1 where
  g := ρ.g
  h := ρ.h
  x0 := ρ.x0
  xr := ρ.xr
  x := fun _ => ∑ i, r i * ρ.x i
  uv := ρ.uv

/-- Length of the combined tag-coefficient list for `linCombCollapse`: the
maximum of the per-attribute `uv` list lengths. Beyond this length every
`(ρA i).uv.getD k (0,0)` is `(0,0)`, so both sides of the evaluation bridge
contribute `0` to that tag position (via `List.getD`'s default). -/
def linCombCollapseUVLen (ρA : Fin n → AGMRepr F n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i => ((ρA i).uv).length

/-- Combined 1-attribute representation of the weighted element
`Σᵢ rᵢ • Aᵢ`, where each `Aᵢ` carries the `n`-attribute representation `ρA i`.
Against the 1-attribute basis `(g₀, H, X₀, Xᵣ, fun _ => X₁)` it evaluates to
`Σᵢ rᵢ • (ρA i).eval` against the embedded basis
`(g₀, H, X₀, Xᵣ, fun j => rⱼ • X₁)` — the dictionary the `help` arm of the
`n → 1` wrapper uses to collapse an `n`-attribute help query.

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
    (∑ i, r i * ((ρA i).uv.getD k (0,0)).1,
     ∑ i, r i * ((ρA i).uv.getD k (0,0)).2)

end KVAC.Schemes.MicroCMZ
