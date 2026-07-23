/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import VCVio

/-!
# μCMZ sign-mask uniformity (O24 §5.3)

Per-query output-distribution lemmas for the sign arm: sampling the non-vanishing
signing masks and forming the code tag has, per query, the same law as the real
oracle's `U ←$ {g // g ≠ 0}`. These are distributional facts only; the downstream
security use — a future `AGMPolynomial`-based reduction consuming them by name — is
deferred (`AGMReduction` does not exist yet). Kept in their own `AGMPolynomial`-free
module so that reduction (which imports `MvPolynomial`) can reuse them without
re-elaborating the proofs in an `MvPolynomial`-heavy instance context, where the
`$ᵗ`-subtype samples below would loop `SampleableType` / `Fintype` search. Imports
only `AlgebraicMAC.lean` (for `glog` / `gen_ne_zero` / `glog_smul`) and `VCVio`.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- `uniformNonzero` is the value-projected subtype sample, in `map` form. -/
private lemma uniformNonzero_eq_map :
    uniformNonzero G
      = Subtype.val <$> ($ᵗ {g : G // g ≠ 0} : ProbComp {g : G // g ≠ 0}) := by
  rfl

/-! ## Sign-mask uniformity

These lemmas establish a single-query output law: sampling `Uⱼ = aᵤ·gen + bᵤ·X`
(non-vanishing masks, `X = x·gen`) is uniform over `G^×`, matching the real oracle's
`U ←$ {g // g ≠ 0}`. They are facts about one query's output distribution; composing
them into a full reduction / transcript coupling is deferred. -/

/-- `SampleableType` for the signing masks `(aᵤ, bᵤ)` whose tag
`Uⱼ = aᵤ·gen + bᵤ·X` is nonzero: a `Fintype` subtype, nonempty via `(1, 0)` since
`gen ≠ 0`. Sampling masks here makes `Uⱼ` uniform over `G^×`, and the `bᵤ`-marginal
stays uniform (`sign_U_bu_dist_eq`). Conditioning on `Uⱼ ≠ 0` *correlates* `(aᵤ, bᵤ)`
(each `b` excludes one `a`), so the Schwartz–Zippel `+1/p` argument under that
conditioned law is *not* established here — it is deferred to the reduction. -/
noncomputable instance instSampleableNonVanishingMasks (X : G) :
    SampleableType {p : F × F // p.1 • gen + p.2 • X ≠ 0} :=
  SampleableType.ofNonemptySubtype (fun p : F × F => p.1 • gen + p.2 • X ≠ 0)
    ⟨⟨(1, 0), by simp only [one_smul, zero_smul, add_zero]; exact gen_ne_zero (gen := gen)⟩⟩

/-- **Opaque wrapper for the sign-mask sample,** definitionally
`$ᵗ {(aᵤ,bᵤ) // Uⱼ ≠ 0}`. Kept named and `irreducible` so a future reduction can
reason about the `sign` branch through the `sign_*_dist_eq` characterizations below
without elaborating the raw `$ᵗ` (whose `SampleableType` search loops in an
`MvPolynomial`-heavy import context); `irreducible` stops `whnf` from unfolding it
back. -/
@[irreducible] noncomputable def reductionMaskSample (X : G) :
    ProbComp {p : F × F // p.1 • gen + p.2 • X ≠ 0} :=
  ($ᵗ {p : F × F // p.1 • gen + p.2 • X ≠ 0} :
    ProbComp {p : F × F // p.1 • gen + p.2 • X ≠ 0})

/-- Forward map of the sign-mask bijection: `(aᵤ, bᵤ) ↦ (⟨Uⱼ, h⟩, bᵤ)` where
`Uⱼ = aᵤ·gen + bᵤ·(x·gen)`. Kept as a bare function so its
bijectivity proof composes cleanly with `evalDist_map_bijective_uniform_cross`. -/
noncomputable def signMaskFun (x : F) :
    {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} →
      ({g : G // g ≠ 0} × F) :=
  fun p => (⟨p.1.1 • gen + p.1.2 • (x • gen), p.2⟩, p.1.2)

/-- **Bijectivity of `signMaskFun`.** The non-vanishing signing masks
`(aᵤ, bᵤ)` (with `Uⱼ = aᵤ·g + bᵤ·(x·g) ≠ 0`) are in bijection with
`{g : G // g ≠ 0} × F`: the map `(aᵤ, bᵤ) ↦ (⟨Uⱼ, h⟩, bᵤ)` is injective
(`Uⱼ = Uⱼ'` and `bᵤ = bᵤ'` force `aᵤ = aᵤ'` via injectivity of `· • gen`)
and surjective (the preimage of `(⟨g, hg⟩, b)` is `(glog g − x·b, b)`, whose
`Uⱼ` is `(glog g) • gen = g` by `glog_smul`). -/
lemma signMaskFun_bijective (x : F) :
    Function.Bijective (signMaskFun (gen := gen) x) := by
  refine ⟨?_, ?_⟩
  · -- injective
    intro p q h
    -- `h : (⟨U_p, _⟩, p.1.2) = (⟨U_q, _⟩, q.1.2)`. Force the explicit `Prod.mk` form
    -- (no `simp`, which loops on the `{g : G // g ≠ 0}` subtype decidability here).
    have h' : ((⟨p.1.1 • gen + p.1.2 • (x • gen), p.2⟩ : {g : G // g ≠ 0}), p.1.2)
        = ((⟨q.1.1 • gen + q.1.2 • (x • gen), q.2⟩ : {g : G // g ≠ 0}), q.1.2) := h
    have hb : p.1.2 = q.1.2 := by
      have := congrArg Prod.snd h'
      exact this
    have hU : p.1.1 • gen + p.1.2 • (x • gen)
        = q.1.1 • gen + q.1.2 • (x • gen) := by
      have := congrArg Subtype.val (congrArg Prod.fst h')
      exact this
    -- From `hU` and `hb`: cancel the common `q.1.2 • (x • gen)` term to get
    -- `p.1.1 • gen = q.1.1 • gen`, hence `(p.1.1 - q.1.1) • gen = 0`.
    have hkey : (p.1.1 - q.1.1) • gen = 0 := by
      rw [hb] at hU
      have hpa : p.1.1 • gen = q.1.1 • gen := add_right_cancel hU
      rw [sub_smul, hpa, sub_self]
    have hdiff : p.1.1 - q.1.1 = 0 :=
      (smul_eq_zero.mp hkey).resolve_right (gen_ne_zero (gen := gen))
    exact Subtype.ext (Prod.ext (sub_eq_zero.mp hdiff) hb)
  · -- surjective
    rintro ⟨⟨g, hg⟩, b⟩
    -- The preimage of `(⟨g, hg⟩, b)` is `(glog g - x·b, b)`, whose `U` is `g`.
    have hkey : (glog gen g - x * b) • gen + b • (x • gen) = g := by
      have hb : b • (x • gen) = (x * b) • gen := by
        rw [smul_smul, mul_comm b x]
      rw [sub_smul, hb, sub_add_cancel, glog_smul]
    refine ⟨⟨(glog gen g - x * b, b), hkey.symm ▸ hg⟩, ?_⟩
    -- forward map roundtrips to the target
    show ((signMaskFun (gen := gen) x) ⟨(glog gen g - x * b, b), hkey.symm ▸ hg⟩)
        = ((⟨g, hg⟩, b) : {g : G // g ≠ 0} × F)
    simp only [signMaskFun, hkey]

/-- The non-vanishing signing masks `(aᵤ, bᵤ)` (with `Uⱼ = aᵤ·g + bᵤ·(x·g) ≠ 0`)
are in bijection with `{g : G // g ≠ 0} × F`. See `signMaskFun_bijective`. -/
noncomputable def signMaskEquiv (x : F) :
    {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} ≃
      ({g : G // g ≠ 0} × F) :=
  Equiv.ofBijective (signMaskFun (gen := gen) x) (signMaskFun_bijective (gen := gen) x)

/-- **Sign-coupling core: masked tag `Uⱼ` is uniform over `G^×`.** Sampling the
non-vanishing masks and projecting `Uⱼ = aᵤ·gen + bᵤ·X` (`X = x·gen`) has exactly the
real oracle's `U ←$ {g // g ≠ 0}` law: uniform over `G^×`. Proved by pointwise
`probOutput` fiber-counting: for `y ≠ 0` the fiber `{(aᵤ,bᵤ) // Uⱼ = y}` has `|F|`
elements via the bijection `signMaskEquiv : {(aᵤ,bᵤ) // Uⱼ≠0} ≃ {g // g ≠ 0} × F`
(one `g = ⟨y, hy⟩`, times `|F|` choices of `bᵤ`), matching `1/|{g ≠ 0}|`; for `y = 0`
both sides vanish. A per-query output law; the security use is deferred. -/
lemma sign_U_dist_eq (x : F) :
    evalDist ((fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
        p.val.1 • gen + p.val.2 • (x • gen)) <$>
        reductionMaskSample (gen := gen) (x • gen))
      = evalDist (uniformNonzero G) := by
  -- Pointwise `probOutput` equality, avoiding the `$ᵗ ({g : G // g ≠ 0} × F)`
  -- product sample (whose `SampleableType` / `Fintype` search loops here).
  rw [reductionMaskSample]
  apply evalDist_ext
  intro y
  -- Both sides: `Pr[= y | U <$> $ᵗM]` and `Pr[= y | uniformNonzero G]`.
  -- Case `y = 0`: `U` never hits `0` (the masks are non-vanishing) and
  -- `Subtype.val` never hits `0` (by `g ≠ 0`); both sides `0`.
  by_cases hy : y = 0
  · -- LHS: `U p = 0` is impossible (the mask's defining property).
    have hL : Pr[= y | (fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
        p.val.1 • gen + p.val.2 • (x • gen))
        <$> ($ᵗ _ : ProbComp _)] = 0 := by
      rw [probOutput_eq_zero_iff, support_map, support_uniformSample,
        Set.image_univ, Set.mem_range]
      rintro ⟨p, hp⟩
      exact absurd (hy ▸ hp) p.property
    -- RHS: `Subtype.val` of a nonzero `g` is nonzero.
    have hR : Pr[= y | uniformNonzero G] = 0 := by
      rw [uniformNonzero_eq_map, probOutput_eq_zero_iff, support_map, support_uniformSample,
        Set.image_univ, Set.mem_range]
      rintro ⟨g, hg⟩
      exact absurd (hy ▸ hg) g.property
    rw [hL, hR]
  · -- `y ≠ 0`: each such `y` has exactly `|F|` preimage masks, so
    -- `Pr[= y | U <$> $ᵗM] = |F| / |M| = 1 / |{g ≠ 0}|`. Count the fiber via
    -- `signMaskEquiv x : M ≃ {g ≠ 0} × F`, not a `glog`-based fiber map: a bare
    -- `glog y` unfolds `glog` and re-elaborates `hgen`, the landmine that keeps
    -- `glog`'s proof in this layer. `Fintype.card` here is pure `Finset`/`Fintype`.
    set M := {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0}
    set U : M → G := fun p => p.val.1 • gen + p.val.2 • (x • gen)
    -- `|M| = |F| · |{g ≠ 0}|` via `signMaskEquiv x : M ≃ {g ≠ 0} × F`.
    have hcardM : Fintype.card M = Fintype.card F * Fintype.card {g : G // g ≠ 0} := by
      rw [Fintype.card_congr (signMaskEquiv (gen := gen) x), Fintype.card_prod, mul_comm]
    -- The fiber `{p : M | U p = y}` ≃ `{q : {g≠0}×F | q.1.val = y}` (restrict
    -- `signMaskEquiv x`), and the latter has `|F|` elements (one `g = ⟨y, hy⟩`, ×
    -- `|F|` choices of `bᵤ`).
    have hcardFiber : Fintype.card {p : M | U p = y} = Fintype.card F := by
      -- `{p : M | U p = y}` ≃ `{q : {g≠0}×F | q.1.val = y}` via `signMaskEquiv x`
      -- (since `U p = ((signMaskEquiv (gen := gen) x) p).1.val`, definitionaly).
      have heq : {p : M | U p = y} ≃
          {q : {g : G // g ≠ 0} × F | q.1.val = y} :=
        Equiv.subtypeEquiv (signMaskEquiv (gen := gen) x) (fun _ => Iff.rfl)
      rw [Fintype.card_congr heq]
      change Fintype.card {q : {g : G // g ≠ 0} × F // (q.1 : G) = y} = Fintype.card F
      -- The latter subtype has `|F|` elements: one `g = ⟨y, hy⟩`, × `|F|` choices of `bᵤ`.
      have hprod := @Equiv.prodSubtypeFstEquivSubtypeProd {g : G // g ≠ 0} F
        (fun g => (g : G) = y)
      rw [Fintype.card_congr hprod, Fintype.card_prod]
      -- The subtype `{g : {g≠0} // (g : G) = y}` is a singleton: the only `g` with
      -- `(g : G) = y` (and `g ≠ 0`, since `y ≠ 0`) is `⟨y, hy⟩`.
      haveI : Unique {g : {g : G // g ≠ 0} // (g : G) = y} :=
        ⟨⟨⟨y, hy⟩, rfl⟩, fun ⟨g, hg⟩ => Subtype.ext (Subtype.val_injective hg)⟩
      rw [Fintype.card_unique, one_mul]
    -- LHS: `Pr[= y | U <$> $ᵗM]` = `#{p | U p = y} / |M|` = `|F| / (|F| · |{g≠0}|)`.
    have hL : Pr[= y | U <$> ($ᵗ M : ProbComp M)] =
        (Fintype.card F : ℝ≥0∞) /
          (Fintype.card F * Fintype.card {g : G // g ≠ 0}) := by
      rw [probOutput_map_eq_sum_fintype_ite]
      simp only [probOutput_uniformSample]
      rw [← Finset.sum_filter, Finset.sum_const]
      simp only [nsmul_eq_mul]
      -- `{a | y = U a}.card = Fintype.card {p | U p = y} = |F|` (hcardFiber).
      have hcf : (Finset.univ.filter (fun a => y = U a)).card = Fintype.card F := by
        rw [← Fintype.card_subtype]
        exact hcardFiber ▸ Fintype.card_congr
          (Equiv.subtypeEquiv (Equiv.refl _) (fun _ => eq_comm))
      rw [hcf, hcardM, div_eq_mul_inv, Nat.cast_mul]
    -- RHS: `Pr[= y | uniformNonzero G]` = `1 / |{g≠0}|`.
    -- For `y ≠ 0`, exactly one `g = ⟨y, hy⟩` maps to `y`; so the fiber has card `1`.
    have hR : Pr[= y | uniformNonzero G] =
        (Fintype.card {g : G // g ≠ 0} : ℝ≥0∞)⁻¹ := by
      rw [uniformNonzero_eq_map, probOutput_map_eq_sum_fintype_ite]
      simp only [probOutput_uniformSample]
      rw [← Finset.sum_filter, Finset.sum_const]
      simp only [nsmul_eq_mul]
      -- The fiber `{g : {g≠0} | (g : G) = y}` is a singleton.
      haveI : Unique {g : {g : G // g ≠ 0} // y = (g : G)} :=
        ⟨⟨⟨y, hy⟩, rfl⟩, fun ⟨g, hg⟩ => Subtype.ext (Subtype.val_injective hg.symm)⟩
      rw [← Fintype.card_subtype, Fintype.card_unique, Nat.cast_one, one_mul]
    rw [hL, hR]
    -- Goal: `|F| / (|F| · |{g≠0}|) = |{g≠0}|⁻¹`.
    -- Via `ENNReal.mul_div_mul_left` (with `a = 1`): `c·1/(c·b) = 1/b`, and `1/b = b⁻¹`.
    have hF : (↑(Fintype.card F) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hF' : (↑(Fintype.card F) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hkey := ENNReal.mul_div_mul_left 1 ↑(Fintype.card {g : G // g ≠ 0}) hF hF'
    rw [mul_one] at hkey
    exact hkey.trans (one_div _)

/-- **Masked tag = honest tag (`AGMPolynomial`-free).** Sampling the non-vanishing
masks and forming the honest pair `(U, key·U)` at `U = aᵤ·g + bᵤ·X` (`X = x·g`) has
exactly the law of `(U ←$ {g ≠ 0}; (U, key·U))`: both are
`(fun g => (g, key·g)) <$> uniformNonzero G`, and the `U`-laws agree by
`sign_U_dist_eq`. This builds the honest pair *directly*; rewriting Eq. 14's degree-2
tag `Vⱼ` (in the 3-DL challenge bases) to `key·U` — and hence the coupling to the
paper's simulator — is the reduction's obligation and is deferred. The mask sample is
the opaque `reductionMaskSample`, so a future reduction can apply this by name without
surfacing the raw `$ᵗ`. -/
lemma sign_masked_tag_dist_eq (x key : F) :
    evalDist ((fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
        ((p.val.1 • gen + p.val.2 • (x • gen),
          key • (p.val.1 • gen + p.val.2 • (x • gen))) : G × G)) <$>
        reductionMaskSample (gen := gen) (x • gen))
      = evalDist (do
          let U ← uniformNonzero G
          pure ((U, key • U) : G × G)) := by
  -- Both sides factor as `(fun g => (g, key·g)) <$> (U-distribution)`.
  have hLHS :
      ((fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
        ((p.val.1 • gen + p.val.2 • (x • gen),
          key • (p.val.1 • gen + p.val.2 • (x • gen))) : G × G)) <$>
        reductionMaskSample (gen := gen) (x • gen))
        = (fun g : G => (g, key • g)) <$>
            ((fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
              p.val.1 • gen + p.val.2 • (x • gen)) <$>
              reductionMaskSample (gen := gen) (x • gen)) := by
    rw [Functor.map_map]
  have hRHS :
      (do
          let U ← uniformNonzero G
          pure ((U, key • U) : G × G))
        = (fun g : G => (g, key • g)) <$> uniformNonzero G := by
    rw [bind_pure_comp]
  rw [hLHS, hRHS,
    evalDist_map ((fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
      p.val.1 • gen + p.val.2 • (x • gen)) <$>
      reductionMaskSample (gen := gen) (x • gen))
      (fun g : G => (g, key • g)),
    evalDist_map (uniformNonzero G)
      (fun g : G => (g, key • g)),
    sign_U_dist_eq (gen := gen) x]

/-- **`(U, bᵤ)` joint distribution under the sign shear.** The non-vanishing masks
`(aᵤ, bᵤ) ←$ {U ≠ 0}` have the same `(U, bᵤ)` joint law as a free pair
`U ←$ {g ≠ 0}`, `bᵤ ←$ F`, via the shear `signMaskEquiv x : {U ≠ 0} ≃ {g ≠ 0} × F`
with `bᵤ` the free second factor. The joint analogue of `sign_U_dist_eq` (which
keeps only the `U` marginal); stated with `uniformNonzero G` and a separate `$ᵗ F`
(never the product, which loops `SampleableType` search) and `glog`-free. Gives the
`(U, bᵤ)` independence the forthcoming Schwartz–Zippel argument needs — necessary but
not sufficient for that bound; the SZ step itself is deferred to the reduction. -/
lemma sign_U_bu_dist_eq (x : F) :
    evalDist ((fun p : {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} =>
        (p.val.1 • gen + p.val.2 • (x • gen), p.val.2)) <$>
        reductionMaskSample (gen := gen) (x • gen))
      = evalDist (do
          let U ← uniformNonzero G
          let bu ← ($ᵗ F : ProbComp F)
          pure ((U, bu) : G × F)) := by
  rw [reductionMaskSample]
  apply evalDist_ext
  rintro ⟨y, bu₀⟩
  set M := {p : F × F // p.1 • gen + p.2 • (x • gen) ≠ 0} with hM
  set Uf : M → G := fun p => p.val.1 • gen + p.val.2 • (x • gen) with hUf
  have hcardM : Fintype.card M = Fintype.card F * Fintype.card {g : G // g ≠ 0} := by
    rw [Fintype.card_congr (signMaskEquiv (gen := gen) x), Fintype.card_prod, mul_comm]
  by_cases hy : y = 0
  · have hL : Pr[= (y, bu₀) | (fun p : M => (Uf p, p.val.2)) <$> ($ᵗ M : ProbComp M)] = 0 := by
      rw [probOutput_eq_zero_iff, support_map, support_uniformSample, Set.image_univ,
        Set.mem_range]
      rintro ⟨p, hp⟩
      rw [Prod.ext_iff] at hp
      exact absurd (hy ▸ hp.1) p.property
    have hU0 : Pr[= (0 : G) | uniformNonzero G] = 0 := by
      rw [uniformNonzero_eq_map, probOutput_eq_zero_iff, support_map, support_uniformSample,
        Set.image_univ, Set.mem_range]
      rintro ⟨g, hg⟩
      exact absurd (hy ▸ hg) g.property
    have hR : Pr[= (y, bu₀) | do
          let U ← uniformNonzero G; let bu ← ($ᵗ F); pure ((U, bu) : G × F)] = 0 := by
      rw [hy]
      simp only [probOutput_bind_bind_prod_mk_eq_mul', id_map']
      rw [hU0, zero_mul]
    rw [hL, hR]
  · -- `y ≠ 0`: the fiber is a singleton; both sides `1/(|F|·|{g≠0}|)`.
    have hL : Pr[= (y, bu₀) | (fun p : M => (Uf p, p.val.2)) <$> ($ᵗ M : ProbComp M)] =
        (Fintype.card F : ℝ≥0∞)⁻¹ * (Fintype.card {g : G // g ≠ 0} : ℝ≥0∞)⁻¹ := by
      rw [probOutput_map_eq_sum_fintype_ite]
      simp only [probOutput_uniformSample]
      rw [← Finset.sum_filter, Finset.sum_const]
      simp only [nsmul_eq_mul]
      -- Fiber `#{p : M | (y, bu₀) = (Uf p, p.val.2)} = 1`
      -- via `signMaskEquiv` + product-of-`Unique`.
      have hcf : (Finset.univ.filter (fun p : M => (y, bu₀) = (Uf p, p.val.2))).card = 1 := by
        rw [← Fintype.card_subtype]
        -- Convert the pair-equality subtype to a conjunction (`Prod.ext_iff`).
        have heqPair : {p : M // (y, bu₀) = (Uf p, p.val.2)} ≃
            {p : M // y = Uf p ∧ bu₀ = p.val.2} :=
          Equiv.subtypeEquiv (Equiv.refl _) (fun _ => Prod.ext_iff)
        rw [Fintype.card_congr heqPair]
        have heq : {p : M // y = Uf p ∧ bu₀ = p.val.2} ≃
            {q : {g : G // g ≠ 0} × F // y = (q.1 : G) ∧ bu₀ = q.2} :=
          Equiv.subtypeEquiv (signMaskEquiv (gen := gen) x) (fun _ => Iff.rfl)
        rw [Fintype.card_congr heq]
        have hprod := @Equiv.subtypeProdEquivProd {g : G // g ≠ 0} F
          (fun g => y = (g : G)) (fun b => bu₀ = b)
        rw [Fintype.card_congr hprod, Fintype.card_prod]
        haveI : Unique {g : {g : G // g ≠ 0} // y = (g : G)} :=
          ⟨⟨⟨y, hy⟩, rfl⟩, fun ⟨⟨g, _⟩, h⟩ => Subtype.ext (Subtype.val_injective h.symm)⟩
        haveI : Unique {b : F // bu₀ = b} :=
          ⟨⟨bu₀, rfl⟩, fun ⟨b, h⟩ => Subtype.ext h.symm⟩
        rw [Fintype.card_unique, Fintype.card_unique, one_mul]
      rw [hcf, hcardM, Nat.cast_mul, Nat.cast_one, one_mul,
        ← ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
          (Or.inl (ENNReal.natCast_ne_top _))]
    have hR : Pr[= (y, bu₀) | do
          let U ← uniformNonzero G; let bu ← ($ᵗ F); pure ((U, bu) : G × F)] =
        (Fintype.card F : ℝ≥0∞)⁻¹ * (Fintype.card {g : G // g ≠ 0} : ℝ≥0∞)⁻¹ := by
      -- `id_map'` collapses the identity `<$>` the marginal split leaves on each factor.
      simp only [probOutput_bind_bind_prod_mk_eq_mul', id_map']
      have hUy : Pr[= y | uniformNonzero G] =
          (Fintype.card {g : G // g ≠ 0} : ℝ≥0∞)⁻¹ := by
        rw [uniformNonzero_eq_map, probOutput_map_eq_sum_fintype_ite]
        simp only [probOutput_uniformSample]
        rw [← Finset.sum_filter, Finset.sum_const]
        simp only [nsmul_eq_mul]
        haveI : Unique {g : {g : G // g ≠ 0} // y = (g : G)} :=
          ⟨⟨⟨y, hy⟩, rfl⟩, fun ⟨g, h⟩ => Subtype.ext (Subtype.val_injective h.symm)⟩
        rw [← Fintype.card_subtype, Fintype.card_unique, Nat.cast_one, one_mul]
      rw [hUy, probOutput_uniformSample, mul_comm]  --mul_comm flips to match RHS
    rw [hL, hR]


end KVAC.Schemes.MicroCMZ
