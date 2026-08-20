/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import VCVio.ProgramLogic.Relational.Basic

/-!
# μCMZ AGM unforgeability — coupling bricks and the Schwartz–Zippel static core

The first probability-layer slice on top of `AGMReduction/Core.lean`:

- `RedLog` normal forms — `rfl` bridges from `Core`'s packaged mask projections
  and substitution down to the per-index lambdas the coupling lemmas use;
- uniformity of the embedded group elements (`evalDist_{smul,affine}_gen_uniform`);
- `relTriple_map_eq`, the deterministic-map coupling brick for the `sign` arm;
- `redLogHonestInv`, the reduction ↔ honest state invariant, and its `maskedKey`;
- the **static** (view-independent) Schwartz–Zippel bound: the `C★` shift lemma,
  the cardinality core `card_filter_eval_eq_zero_le`, and its probability form
  `probEvent_eval_shift_eq_zero_le`.

The distribution-layer bad-event bound built on these lives further down the
stack; see `AGMReduction.lean`.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
/- The generator `G₀` (O24's `G₀ ∈ Γ`); see the note in `AGMReduction/Core.lean`. -/
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-! ## `RedLog` normal forms

`Core`'s oracle bodies carry the packaged projections (`L.aMask`, …) and the
substitution they bundle into (`maskedRepr`, `maskedSubst`); the coupling lemmas,
`C★`, `eval_affineSubst` and `recoverDlog_verifPoly_eq` all speak per-index
lambdas and `AGMPoly.affineSubst`. Both forms are plain `def`s, so `exact` sees
through them but `rw`/`simp only` do not. These `rfl` bridges close the gap —
stated *unapplied*, so `simp` catches the partially-applied occurrences the
oracle bodies produce, and public because every later part of the reduction
consumes them. The chain `maskedRepr → maskedSubst → affineSubst → per-index
lambdas` then runs in one `simp only`. -/

namespace RedLog

section NormalForms
-- `RedLog`/`SignRecord` are plain data: none of the algebraic or sampling
-- structure on `F`/`G` is involved in these `rfl`s.
omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G]
  [SampleableGroup F G]

/-- The `a`-side per-query mask, unapplied. -/
lemma aMask_def (L : RedLog F G) :
    L.aMask = fun j => (L.get j).au := rfl

/-- The `b`-side per-query mask, unapplied. -/
lemma bMask_def (L : RedLog F G) :
    L.bMask = fun j => (L.get j).bu := rfl

/-- The per-query message, unapplied. -/
lemma msg_def (L : RedLog F G) :
    L.msg = fun j => (L.get j).msg 0 := rfl

/-- The issued tags, unapplied. -/
lemma tags_def (L : RedLog F G) :
    L.tags = L.map (fun e => e.tag) := rfl

end NormalForms

section MaskedSubstNormalForms
-- Unlike the projections above, these mention `AGMPoly`/`Polynomial` and so keep `Field F`.
omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G]

/-- The packaged substitution — the form `microCMZ3DLReduction` emits its `ψ` in — in the
`affineSubst` form everything downstream is stated in. -/
lemma maskedSubst_def (L : RedLog F G) (aM bM : FixedMasks F) :
    L.maskedSubst aM bM = AGMPoly.affineSubst (aM.embed L.aMask) (bM.embed L.bMask) := rfl

/-- A representation pushed through the substitution. One step, to `maskedSubst` rather than
straight to `affineSubst`, so that
`simp only [maskedRepr_def, maskedSubst_def, aMask_def, bMask_def]` walks the whole chain. -/
lemma maskedRepr_def (L : RedLog F G) (aM bM : FixedMasks F) (ρ : AGMRepr F 1) :
    L.maskedRepr aM bM ρ = L.maskedSubst aM bM ((ρ.toReprCoeffs L.length).toPoly L.msg) := rfl

end MaskedSubstNormalForms

end RedLog

/-! ## Uniformity of the embedded elements (coupling bricks) -/

/-- `(· • gen)` is a bijection, so it pushes `$ᵗ F` to `$ᵗ G`. The unshifted case, for the
issued tag base `Uⱼ = (auⱼ + x·buⱼ) • gen`. -/
lemma evalDist_smul_gen_uniform :
    evalDist ((fun a : F => a • gen) <$> ($ᵗ F : ProbComp F)) =
      evalDist ($ᵗ G : ProbComp G) :=
  evalDist_map_bijective_uniform_cross (α := F) _ hgen.out

/-- Shift by `c`, then scale the generator: a composition of bijections. The reduction's `H`,
`Xᵣ`, `X₁` all have this affine form, so they are uniform just like `AGM_UF_CMVAGame`'s. -/
lemma evalDist_affine_gen_uniform (c : F) :
    evalDist ((fun a : F => (a + c) • gen) <$> ($ᵗ F : ProbComp F)) =
      evalDist ($ᵗ G : ProbComp G) := by
  exact evalDist_map_bijective_uniform_cross (α := F) _
    (hgen.out.comp (Equiv.addRight c).bijective)

section RelationalCoupling
open OracleComp.ProgramLogic.Relational

variable {ι₁ ι₂ : Type} {specR₁ : OracleSpec ι₁} {specR₂ : OracleSpec ι₂}
variable [IsUniformSpec specR₁] [IsUniformSpec specR₂]

/-- **Deterministic map coupling.** If `f <$> a` matches `b` in distribution, then `a` and `b`
are coupled by `f x = y`. Witness: the graph coupling `evalDist a >>= fun x => pure (x, f x)`.

The per-query brick for the `sign` arm (`reductionSignStep` vs `agmOracleImpl (.sign _)`):
`embedTag_eq` puts the reduction's tag in the honest shape `(U, key·U)` and
`sign_masked_tag_dist_eq` matches its distribution to `mac`'s; this lifts that equality to
“computed tag = sampled tag”, for `relTriple_bind` to thread through the log append. -/
lemma relTriple_map_eq {α β : Type} (a : OracleComp specR₁ α) (f : α → β)
    (b : OracleComp specR₂ β) (h : evalDist (f <$> a) = evalDist b) :
    RelTriple a b (fun x y => f x = y) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  refine ⟨⟨evalDist a >>= fun x => pure (x, f x), ?_⟩, ?_⟩
  · constructor
    · -- map_fst : Prod.fst <$> (evalDist a >>= fun x => pure (x, f x)) = evalDist a
      simp only [map_bind, map_pure]
      change (fun x : α => x) <$> evalDist a = evalDist a
      simp only [id_map']
    · -- map_snd : Prod.snd <$> (evalDist a >>= fun x => pure (x, f x)) = evalDist b
      simp only [map_bind, map_pure]
      change (fun x : α => f x) <$> evalDist a = evalDist b
      rw [← evalDist_map, h]
  · rintro ⟨x, y⟩ hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨x', hx', hz'⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz'
    obtain ⟨hxeq, hyeq⟩ : x = x' ∧ y = f x' := Prod.ext_iff.mp hz'
    rw [hxeq, hyeq]

end RelationalCoupling

/-! ## B2 oracle coupling (reduction ↔ honest) -/

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
/-- The honest key at the challenge exponent: each `Key F 1` component read at the masked
secrets `xₖ = aₖ + x·bₖ`. `abbrev`, so `rw`/`simp only` see through it. -/
abbrev maskedKey (x : F) (aM bM : FixedMasks F) : Key F 1 :=
  (aM.x0 + x * bM.x0, aM.xr + x * bM.xr, fun _ => aM.x1 + x * bM.x1)

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
/-- `Core`'s `macScalar_eq_keyCoeff` for an arbitrary `m : Fin 1 → F`: the bridge from the honest
form `redLogHonestInv` is stated in to the `keyCoeff` form `embedTag_eq` consumes. -/
lemma macScalar_maskedKey_eq (aM bM : FixedMasks F) (x : F) (m : Fin 1 → F) :
    macScalar (maskedKey x aM bM) m = aM.keyCoeff (m 0) + x * bM.keyCoeff (m 0) := by
  simp only [macScalar, FixedMasks.keyCoeff, Fin.sum_univ_one]
  ring

/-- The reduction↔honest state invariant for the two-impl `simulateQ` coupling.

First conjunct: both impls append one entry per `sign` query in order, so the honest log is the
reduction log with the masks projected away. Second: per entry, the embedded base form
`Uⱼ = auⱼ·g + buⱼ·X` (`Core`'s `embedMask_eq`) and `MicroCMZ.verify`'s own tag relation read at
`maskedKey`. The tag relation is stated through `macScalar` rather than expanded by hand, so it
stays in step with `Construction.lean` and is literally what the honest `sign` arm emits;
`macScalar_maskedKey_eq` converts it to the `keyCoeff` form `embedTag_eq` consumes. -/
def redLogHonestInv (x : F) (aM bM : FixedMasks F) (L : RedLog F G) (log : AGMLog F G 1) : Prop :=
  log = L.map (fun e => (e.msg, e.tag)) ∧
  ∀ e ∈ L, e.tag.1 = e.au • gen + e.bu • (x • gen) ∧
           e.tag.2 = macScalar (maskedKey x aM bM) e.msg • e.tag.1

/-! ## Schwartz–Zippel bad-event bound (Piece C) -/

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- **C★.** `ψ ≡ 0` ⇒ `ψ(x+1) = 0`, which by `eval_affineSubst` says `φ` vanishes at the real-log
point shifted by `b`. This is what lets Schwartz–Zippel hit `φ = verifPoly` *directly*, with no
top-coefficient / homogeneous-component lemma. -/
lemma eval_shift_eq_zero_of_affineSubst_eq_zero {q : ℕ} (a b : AGMPoly.Var q → F)
    (x : F) (φ : AGMPoly.P F q) (h : AGMPoly.affineSubst a b φ = 0) :
    MvPolynomial.eval (fun v => a v + (x + 1) * b v) φ = 0 := by
  have key := AGMPoly.eval_affineSubst a b (x + 1) φ
  rw [h, Polynomial.eval_zero] at key
  exact key.symm

omit [SampleableType F] in
/-- A bijection `wOf : (Fin N → F) → (Var q → F)` preserves the count of vanishing points. Used
twice below: bare, to transport the Schwartz–Zippel count off `Fin N`, and composed with a
translation, to absorb the uniform shift. -/
private lemma card_filter_eval_wOf_eq {q : ℕ} (φ : AGMPoly.P F q)
    (wOf : (Fin (Fintype.card (AGMPoly.Var q)) → F) → (AGMPoly.Var q → F))
    (hbij : Function.Bijective wOf) :
    (Finset.univ.filter (fun b : Fin (Fintype.card (AGMPoly.Var q)) → F =>
        MvPolynomial.eval (wOf b) φ = 0)).card
      = (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective wOf hbij) (fun b => by
    simp only [Equiv.ofBijective_apply]))

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Reindexing `Fin (#Var q) → F` to `Var q → F` along `Fintype.equivFin`: the `wOf` both uses
of `card_filter_eval_wOf_eq` are built from. -/
private lemma reindexMasks_bijective {q : ℕ} :
    Function.Bijective (fun b : Fin (Fintype.card (AGMPoly.Var q)) → F =>
      (fun v => b (Fintype.equivFin (AGMPoly.Var q) v) : AGMPoly.Var q → F)) :=
  (Equiv.arrowCongr (Fintype.equivFin (AGMPoly.Var q)).symm (Equiv.refl F)).bijective

omit [SampleableType F] in
/-- **C-SZ (cardinality form).** The combinatorial core of the `3/p` bad event: a nonzero
degree-`≤ 3` `φ` over `Var q → F` vanishes at `card * |F| ≤ 3 * |F|^(#Var q)` points. Wrapper
around `MvPolynomial.schwartz_zippel_totalDegree`, transported off `Fin (#Var q)` via
`Fintype.equivFin` / `MvPolynomial.rename`.

Deliberately stated **without** `Pr[…]`/`$ᵗ (Var q → F)`: in this module's import context (the
`MvPolynomial` / `Polynomial` order instances) `probEvent` over a uniform *function-type* sample
sends instance search into a loop. The conversion is done at the use site via
`probEvent_uniformSample`, where the masks are sampled. -/
lemma card_filter_eval_eq_zero_le {q : ℕ} (φ : AGMPoly.P F q) (hφ : φ ≠ 0)
    (hdeg : φ.totalDegree ≤ 3) :
    (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
        * Fintype.card F
      ≤ 3 * Fintype.card F ^ Fintype.card (AGMPoly.Var q) := by
  classical
  set N := Fintype.card (AGMPoly.Var q)
  let e : AGMPoly.Var q ≃ Fin N := Fintype.equivFin (AGMPoly.Var q)
  set p : MvPolynomial (Fin N) F := MvPolynomial.rename e φ with hp_def
  have hp : p ≠ 0 := by
    rw [hp_def]; intro h
    exact hφ (MvPolynomial.rename_injective (e : AGMPoly.Var q → Fin N) e.injective
      (by rw [h, map_zero]))
  have hdegp : p.totalDegree ≤ 3 := by
    rw [hp_def]; exact le_trans (MvPolynomial.totalDegree_rename_le _ _) hdeg
  -- Evaluating `p = rename e φ` at `f` is evaluating `φ` at `f` reindexed along `e`.
  have hEval : ∀ f : Fin N → F,
      MvPolynomial.eval f p = MvPolynomial.eval (fun v => f (e v)) φ := by
    intro f
    rw [hp_def, MvPolynomial.eval_rename]
    rfl
  have hcard : (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
             = (Finset.univ.filter (fun f : Fin N → F => MvPolynomial.eval f p = 0)).card := by
    simp only [hEval]
    exact (card_filter_eval_wOf_eq φ (fun f v => f (e v)) reindexMasks_bijective).symm
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ] at hsz
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hsz
  have hnat : (Finset.univ.filter (fun f : Fin N → F => MvPolynomial.eval f p = 0)).card
        * Fintype.card F ≤ p.totalDegree * Fintype.card F ^ N := by exact_mod_cast hsz
  calc (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
          * Fintype.card F
      = (Finset.univ.filter (fun f : Fin N → F => MvPolynomial.eval f p = 0)).card
          * Fintype.card F := by rw [hcard]
    _ ≤ p.totalDegree * Fintype.card F ^ N := hnat
    _ ≤ 3 * Fintype.card F ^ N := by gcongr

omit [SampleableType F] in
/-- Arithmetic helper: convert the cardinality Schwartz–Zippel bound to the `3/|F|`
rational form. -/
private lemma card_filter_div_le {q : ℕ} (φ : AGMPoly.P F q) (hφ : φ ≠ 0)
    (hdeg : φ.totalDegree ≤ 3) :
    (((Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card : ℝ≥0∞))
        / (Fintype.card F : ℝ≥0∞) ^ Fintype.card (AGMPoly.Var q)
      ≤ 3 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  set N := Fintype.card (AGMPoly.Var q) with hN
  have hsz := card_filter_eval_eq_zero_le φ hφ hdeg
  rw [← hN] at hsz
  set c := (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
  have hpF : Fintype.card F ≠ 0 := Fintype.card_ne_zero
  have hcF : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpF
  have hcFN : (Fintype.card F : ℝ≥0∞) ^ N ≠ 0 := pow_ne_zero _ hcF
  -- Cast the natural-number bound `c * |F| ≤ 3 * |F|^N` into `ℝ≥0∞`.
  have hszE : (c : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)
      ≤ 3 * (Fintype.card F : ℝ≥0∞) ^ N := by
    calc (c : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)
        = ((c * Fintype.card F : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((3 * Fintype.card F ^ N : ℕ) : ℝ≥0∞) := by exact_mod_cast hsz
      _ = 3 * (Fintype.card F : ℝ≥0∞) ^ N := by push_cast; ring
  -- `c / |F|^N ≤ 3 * |F|⁻¹` ⟺ `c * |F| ≤ 3 * |F|^N` (cross-multiply; all factors finite, nonzero).
  rw [ENNReal.div_le_iff hcFN (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)), mul_right_comm]
  calc (c : ℝ≥0∞)
      = (c : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hcF (ENNReal.natCast_ne_top _), mul_one]
    _ ≤ 3 * (Fintype.card F : ℝ≥0∞) ^ N * (Fintype.card F : ℝ≥0∞)⁻¹ := by gcongr

-- `[DecidableEq F]` does not survive into the elaborated type, but it is load-bearing while
-- elaborating it: it is what lets the `DecidablePred` behind `Pr[…]` be found directly. `omit`ting
-- it (as `linter.unusedDecidableInType` suggests) sends that search into this module's documented
-- instance loop and the declaration times out. Scoped to this one declaration.
set_option linter.unusedDecidableInType false in
/-- **C-SZ (probability form).** For a *fixed* offset `θ`, a uniform shift `b` makes the point
`w v = θ v + b (e v)` uniform over `Var q → F` (reindexing by `e := Fintype.equivFin` and
translating by `θ` are both bijections), so `card_filter_eval_eq_zero_le` bounds the vanishing
probability by `3/|F|`.

`b` is sampled through `Fin (#Var q) → F`, not `Var q → F`: only the `Var q`-indexed uniform
function sample hangs `SampleableType` instance search in this `MvPolynomial`-heavy context.

The reusable analytic core for the shear keystone, where `θ v = a v + x·b v` is the offset, `b`
is the free post-reparametrization mask, and `w = θ + b` is the point C★ forces `φ` to vanish
at. -/
lemma probEvent_eval_shift_eq_zero_le {q : ℕ} (φ : AGMPoly.P F q) (hφ : φ ≠ 0)
    (hdeg : φ.totalDegree ≤ 3) (θ : AGMPoly.Var q → F) :
    Pr[(fun b : Fin (Fintype.card (AGMPoly.Var q)) → F =>
          MvPolynomial.eval
            (fun v => θ v + b ((Fintype.equivFin (AGMPoly.Var q)) v)) φ = 0) |
        ($ᵗ (Fin (Fintype.card (AGMPoly.Var q)) → F))]
      ≤ 3 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  rw [probEvent_uniformSample, Fintype.card_fun, Fintype.card_fin]
  have hbij : Function.Bijective
      (fun b : Fin (Fintype.card (AGMPoly.Var q)) → F =>
        (fun v => θ v + b ((Fintype.equivFin (AGMPoly.Var q)) v) : AGMPoly.Var q → F)) := by
    have h2 : Function.Bijective
        (fun w : AGMPoly.Var q → F => (fun v => θ v + w v : AGMPoly.Var q → F)) :=
      (Equiv.addLeft (θ : AGMPoly.Var q → F)).bijective
    exact h2.comp reindexMasks_bijective
  have hcard := card_filter_eval_wOf_eq φ
    (fun b v => θ v + b ((Fintype.equivFin (AGMPoly.Var q)) v)) hbij
  rw [hcard, Nat.cast_pow]
  exact card_filter_div_le φ hφ hdeg

end KVAC.Schemes.MicroCMZ
