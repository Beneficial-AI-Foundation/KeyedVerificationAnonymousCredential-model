/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-! # AGMReduction Coupling — uniformity/relational bricks, Schwartz–Zippel card bounds -/

/-! ## Uniformity of the embedded elements (coupling bricks) -/

/-- Sampling a scalar and scaling the generator yields a *uniform* group element:
`(· • generator G)` is a bijection, so it pushes `$ᵗ F` to `$ᵗ G`. -/
lemma evalDist_smul_generator_uniform :
    evalDist ((fun a : F => a • generator G) <$> ($ᵗ F : ProbComp F)) =
      evalDist ($ᵗ G : ProbComp G) :=
  evalDist_map_bijective_uniform_cross (α := F) _ smul_generator_bijective

/-- The embedded affine element `a ↦ (a + c) • generator G` is uniform over `G`
when `a ←$ F` — shift by `c` then scale the generator, a composition of
bijections. This is the distribution-matching brick for the coupling with
`AGM_UF_CMVAGame`: the reduction's `H`, `Xᵣ`, `X₁` (and each `Uⱼ`) have exactly
this affine form, so they are uniform just like the real game's. -/
lemma evalDist_affine_generator_uniform (c : F) :
    evalDist ((fun a : F => (a + c) • generator G) <$> ($ᵗ F : ProbComp F)) =
      evalDist ($ᵗ G : ProbComp G) := by
  have hadd : Function.Bijective (fun a : F => a + c) :=
    ⟨fun a b h => add_right_cancel h, fun y => ⟨y - c, by ring⟩⟩
  exact evalDist_map_bijective_uniform_cross (α := F) _
    (smul_generator_bijective.comp hadd)

section RelationalCoupling
open OracleComp.ProgramLogic.Relational

variable {ι₁ ι₂ : Type} {specR₁ : OracleSpec ι₁} {specR₂ : OracleSpec ι₂}
variable [specR₁.Fintype] [specR₁.Inhabited] [specR₂.Fintype] [specR₂.Inhabited]

/-- **Deterministic map coupling.** If `f <$> a` has the same evaluation distribution as `b`,
then `a` and `b` are coupled by the relation `f x = y`: pair each `x ← a` with the deterministic
image `f x`. Witness: the graph coupling `evalDist a >>= fun x => pure (x, f x)`.

This is the per-query coupling brick for the reduction `sign` arm (`reductionSignStep` vs
`agmOracleImpl (.sign _)`): the reduction samples the masks `(au, bu)` and computes the tag
`(U, V) = (U, key·U)` (by `sign_tag_honest`), whose distribution matches `microCMZSign`'s
`(U, key·U)` (by `sign_masked_tag_dist_eq`); `relTriple_map_eq` lifts that `evalDist` equality
to the relation “computed tag = sampled tag”, which `relTriple_bind` then threads through the
state (log) append. -/
lemma relTriple_map_eq {α β : Type} (a : OracleComp specR₁ α) (f : α → β)
    (b : OracleComp specR₂ β) (h : evalDist (f <$> a) = evalDist b) :
    RelTriple a b (fun x y => f x = y) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  refine ⟨⟨evalDist a >>= fun x => pure (x, f x), ?_⟩, ?_⟩
  · constructor
    · -- map_fst : Prod.fst <$> (evalDist a >>= fun x => pure (x, f x)) = evalDist a
      simp only [map_bind, map_pure]
      change (fun x : α => x) <$> evalDist a = evalDist a
      simp
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

section B2Coupling
open OracleComp.ProgramLogic.Relational

/-- The reduction↔honest state invariant for the two-impl `simulateQ` coupling: the honest log is
the reduction log with masks projected away, every logged tag is honest
(`Vⱼ = keyⱼ·Uⱼ` at the real logs `xₖ = aₖ + x·bₖ`), and every logged `Uⱼ` has the embedded form
`Uⱼ = auⱼ·g + buⱼ·X` (so `gamePoint_eq_affine`'s `htagU` holds). The first conjunct is the
structural log correspondence (sign appends match); the second is `redLog_honest`'s invariant,
the third `redLog_U_form`'s — both needed by `represented_value_eq_affineSubst_eval` (hence the
`verify`/`help` bit-equality `exponentEval_verify_eq`). -/
def redRState (x a0 b0 aXr bXr aX1 bX1 : F) (L : RedLog F G) (log : AGMLog F G 1) : Prop :=
  log = L.map (fun e => (e.1, e.2.1)) ∧
  (∀ e ∈ L, e.2.1.2 = ((a0 + x*b0) + (aXr + x*bXr) + e.1 0 * (aX1 + x*bX1)) • e.2.1.1) ∧
  ∀ e ∈ L, e.2.1.1 = e.2.2.1 • generator G + e.2.2.2 • (x • generator G)

end B2Coupling

/-! ## Schwartz–Zippel bad-event bound (Piece C) -/

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- **C★.** If the affine restriction `ψ = affineSubst a b φ` is the *zero polynomial*, then `φ`
vanishes at the shifted real-log point `v ↦ (a v + x·b v) + b v` — evaluate `ψ` at `χ = x + 1`
(`ψ ≡ 0` ⇒ `ψ(x+1) = 0`). One step from the already-proven `eval_affineSubst`. This is what lets
Schwartz–Zippel hit `φ = verifPoly` *directly*, with no top-coefficient / homogeneous-component
lemma: for a fixed view the point `θ + b` is uniform when `b` is. -/
lemma eval_shift_eq_zero_of_affineSubst_eq_zero {q : ℕ} (a b : AGMPoly.Var q → F)
    (x : F) (φ : AGMPoly.P F q) (h : AGMPoly.affineSubst a b φ = 0) :
    MvPolynomial.eval (fun v => a v + (x + 1) * b v) φ = 0 := by
  have key := AGMPoly.eval_affineSubst a b (x + 1) φ
  rw [h, Polynomial.eval_zero] at key
  exact key.symm

omit [SampleableType F] in
/-- **C-SZ (cardinality form).** Schwartz–Zippel for the verification polynomial, stated as a pure
`Finset`/`Fintype` cardinality bound: the number of points where a nonzero degree-`≤ 3`
multivariate polynomial `φ` over `Var q → F` vanishes, times `|F|`, is at most `3·|F|^(#Var q)`.

This is the combinatorial core of the `1/p` (here `3/p`) bad event. It is deliberately stated
**without** `Pr[…]`/`$ᵗ (Var q → F)`: in this module's import context (the `MvPolynomial` /
`Polynomial` order instances) `probEvent` over a uniform *function-type* sample sends instance
search into a loop. The probability conversion `Pr[eval (w ←$ Var q→F) φ = 0] = #filter / |F|^#Var`
is done at the use site via `probEvent_uniformSample`, where the masks are sampled.

Wrapper around `MvPolynomial.schwartz_zippel_totalDegree`, transported from `Fin (#Var q)` to
`Var q` via `Fintype.equivFin` / `MvPolynomial.rename`. -/
lemma card_filter_eval_eq_zero_le {q : ℕ} (φ : AGMPoly.P F q) (hφ : φ ≠ 0)
    (hdeg : φ.totalDegree ≤ 3) :
    (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
        * Fintype.card F
      ≤ 3 * Fintype.card F ^ Fintype.card (AGMPoly.Var q) := by
  classical
  set N := Fintype.card (AGMPoly.Var q) with hN
  let e : AGMPoly.Var q ≃ Fin N := Fintype.equivFin _
  set p : MvPolynomial (Fin N) F := MvPolynomial.rename e φ with hp_def
  have hp : p ≠ 0 := by
    rw [hp_def]; intro h
    exact hφ (MvPolynomial.rename_injective (e : AGMPoly.Var q → Fin N) e.injective
      (by rw [h, map_zero]))
  have hdegp : p.totalDegree ≤ 3 := by
    rw [hp_def]; exact le_trans (MvPolynomial.totalDegree_rename_le _ _) hdeg
  have hEval : ∀ w : AGMPoly.Var q → F,
      MvPolynomial.eval (w ∘ ⇑e.symm) p = MvPolynomial.eval w φ := by
    intro w
    rw [hp_def, MvPolynomial.eval_rename]
    have harg : (w ∘ ⇑e.symm) ∘ ⇑e = w := by funext v; simp
    rw [harg]
  have hcard : (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
             = (Finset.univ.filter (fun f : Fin N → F => MvPolynomial.eval f p = 0)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl F)) ?_)
    intro w
    have hEw : (Equiv.arrowCongr e (Equiv.refl F)) w = w ∘ ⇑e.symm := by
      funext b; simp [Equiv.arrowCongr_apply]
    simp only [hEw, hEval w]
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
/-- Reindexing helper: the `wOf`-bijection `(Fin N → F) → (Var q → F)` preserves the count of
vanishing points (`wOf` ranges over all of `Var q → F` as its argument ranges over `Fin N → F`). -/
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

omit [SampleableType F] in
/-- Arithmetic helper: convert the cardinality Schwartz–Zippel bound to the `3/|F|`
rational form. -/
private lemma szCard_to_prob {q : ℕ} (φ : AGMPoly.P F q) (hφ : φ ≠ 0) (hdeg : φ.totalDegree ≤ 3) :
    (((Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card : ℝ≥0∞))
        / (Fintype.card F : ℝ≥0∞) ^ Fintype.card (AGMPoly.Var q)
      ≤ 3 * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  set N := Fintype.card (AGMPoly.Var q) with hN
  have hsz := card_filter_eval_eq_zero_le φ hφ hdeg
  rw [← hN] at hsz
  set c := (Finset.univ.filter (fun w : AGMPoly.Var q → F => MvPolynomial.eval w φ = 0)).card
    with hc
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
  rw [ENNReal.div_le_iff hcFN (by simp), mul_right_comm]
  calc (c : ℝ≥0∞)
      = (c : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hcF (by simp), mul_one]
    _ ≤ 3 * (Fintype.card F : ℝ≥0∞) ^ N * (Fintype.card F : ℝ≥0∞)⁻¹ := by gcongr

/-- **C-SZ (probability form).** The Schwartz–Zippel bad event as a probability over a uniform
shift. The shift `b` is sampled through `Fin (#Var q) → F` rather than `Var q → F`: only the
`Var q`-indexed uniform function sample hangs `SampleableType` instance search in this module's
`MvPolynomial`-heavy context, while `Fin k → F` is clean. For a fixed offset `θ`, a uniform
`b : Fin (#Var q) → F` makes the point `w v = θ v + b (e v)` uniform over `Var q → F`
(reindexing by `e := Fintype.equivFin` and translating by `θ` are bijections), so
`card_filter_eval_eq_zero_le` bounds the vanishing probability of a nonzero degree-`≤ 3`
polynomial by `3/|F|`.

This is the reusable analytic core for the shear keystone: there the uniform `b` is the free
(post-reparametrization) `b`-masks reindexed to `Fin (#Var q)`, `θ v = a v + x·b v` is the offset,
and `w = θ + b` is the shifted real-log point at which C★ forces `φ` to vanish. -/
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
    have h1 : Function.Bijective
        (fun b : Fin (Fintype.card (AGMPoly.Var q)) → F =>
          (fun v => b ((Fintype.equivFin (AGMPoly.Var q)) v) : AGMPoly.Var q → F)) :=
      (Equiv.arrowCongr (Fintype.equivFin (AGMPoly.Var q)).symm (Equiv.refl F)).bijective
    have h2 : Function.Bijective
        (fun w : AGMPoly.Var q → F => (fun v => θ v + w v : AGMPoly.Var q → F)) :=
      (Equiv.addLeft (θ : AGMPoly.Var q → F)).bijective
    exact h2.comp h1
  have hcard := card_filter_eval_wOf_eq φ
    (fun b v => θ v + b ((Fintype.equivFin (AGMPoly.Var q)) v)) hbij
  rw [hcard, Nat.cast_pow]
  exact szCard_to_prob φ hφ hdeg


end KVAC.Schemes.MicroCMZ
