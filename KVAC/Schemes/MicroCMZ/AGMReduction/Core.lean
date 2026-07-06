/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import KVAC.Schemes.MicroCMZ.AGMPolynomial

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-! # AGMReduction Core — dictionary, eval bridge, adversary B₃, root recovery -/

/-! ## The game ↔ polynomial dictionary -/

/-- Polynomial-layer coefficients of a game-layer `AGMRepr F 1` over a transcript
with `q` issued tags. Tag coefficients past the `q`-th default to `0`, matching
the `zipWith` truncation in `AGMRepr.eval`. -/
def AGMRepr.toReprCoeffs (ρ : AGMRepr F 1) (q : ℕ) : AGMPoly.ReprCoeffs F q where
  cg := ρ.g
  ch := ρ.h
  c0 := ρ.x0
  cr := ρ.xr
  c1 := ρ.x 0
  cu := fun j => (ρ.uv.getD (j : ℕ) (0, 0)).1
  cv := fun j => (ρ.uv.getD (j : ℕ) (0, 0)).2

/-- The discrete-log evaluation point of a μCMZ transcript: each polynomial
variable maps to the `generator G`-discrete-log of the basis element it
abbreviates (`η = log H`, the key components `x₀, xᵣ, x₁`, and `uⱼ = log Uⱼ`). -/
noncomputable def gamePoint (H : G) (x0 xr x1 : F) (tags : List (G × G)) :
    AGMPoly.Var tags.length → F
  | .eta => glog H
  | .x0 => x0
  | .xr => xr
  | .x1 => x1
  | .u j => glog (tags.get j).1

/-- A `zipWith`-sum over two lists equals a `Fin`-indexed sum over the second
list's length, reading the first list with `getD` (default `da`, which `f` sends
to `0`) — this reconciles `AGMRepr.eval`'s `zipWith` tag fold with
`ReprCoeffs.toPoly`'s `∑ : Fin q` over the issued tags. -/
theorem zipWith_smul_sum {α β M : Type*} [AddCommMonoid M] (f : α → β → M)
    (da : α) (db : β) (hf0 : ∀ b, f da b = 0) (la : List α) (lb : List β) :
    (List.zipWith f la lb).sum
      = ∑ j : Fin lb.length, f (la.getD (j : ℕ) da) (lb.get j) := by
  have key : ∀ (la : List α) (lb : List β),
      (List.zipWith f la lb).sum
        = ∑ k ∈ Finset.range lb.length, f (la.getD k da) (lb.getD k db) := by
    intro la lb
    induction lb generalizing la with
    | nil => simp
    | cons b bs ih =>
      cases la with
      | nil =>
        simp only [List.zipWith_nil_left, List.sum_nil, List.getD_nil, hf0,
          Finset.sum_const_zero]
      | cons a tl =>
        rw [List.zipWith_cons_cons, List.sum_cons, ih tl, List.length_cons,
          Finset.sum_range_succ']
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [add_comm]
  rw [key la lb,
    ← Fin.sum_univ_eq_sum_range (fun k => f (la.getD k da) (lb.getD k db)) lb.length]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [List.get_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
  rfl

/-! ## The eval bridge (keystone) -/

/--
**Eval bridge (keystone).** Over an honestly-generated transcript (`htag`: each
issued tag satisfies `Vⱼ = (x₀+xᵣ+mⱼx₁)·Uⱼ`), a representation's group-level
evaluation `AGMRepr.eval` equals the polynomial `ReprCoeffs.toPoly` evaluated at
the transcript's discrete-log point, scaled onto `generator G`.

This is the `AGMRepr ↔ ReprCoeffs` glue the `AGMPolynomial` module docstring
defers ("glue between the two lives with the game"). The proof writes the
uniformly-sampled basis element `H` as `η • generator G` (`smul_generator_surjective`),
reconciles the `zipWith` tag fold with `toPoly`'s `Fin`-sum (`zipWith_smul_sum`),
expands the polynomial evaluation (`ReprCoeffs.eval_toPoly`), and closes the
resulting `generator G`-module identity with `module` (using `htag` for the
`Vⱼ`). -/
theorem agmRepr_eval_eq_eval_toPoly (ρ : AGMRepr F 1) (H : G) (x0 xr : F)
    (x : Fin 1 → F) (tags : List (G × G)) (msgs : Fin tags.length → F)
    (htag : ∀ j : Fin tags.length,
      (tags.get j).2 = (x0 + xr + msgs j * x 0) • (tags.get j).1) :
    ρ.eval (generator G) H (x0 • H) (xr • generator G)
        (fun i => x i • generator G) tags
      = MvPolynomial.eval (gamePoint H x0 xr (x 0) tags)
          ((ρ.toReprCoeffs tags.length).toPoly msgs) • generator G := by
  obtain ⟨η, rfl⟩ := smul_generator_surjective (F := F) H
  rw [AGMRepr.eval, AGMPoly.ReprCoeffs.eval_toPoly,
    zipWith_smul_sum (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2)
      ((0, 0) : F × F) ((0, 0) : G × G) (by intro t; simp) ρ.uv tags]
  simp only [AGMRepr.toReprCoeffs, gamePoint, glog_smul_self, Fin.sum_univ_one]
  rw [add_smul, Finset.sum_smul]
  congr 1
  · module
  · apply Finset.sum_congr rfl
    intro j _
    obtain ⟨u, hu⟩ := smul_generator_surjective (F := F) (tags.get j).1
    rw [htag j, ← hu, glog_smul_self]
    module

/-! ## The identity branch (mechanized) -/

/--
**Identity branch of O24 Lemma 5.4 (mechanized).** If a consistent forgery for a
*fresh* message has a verification polynomial that vanishes identically, then
`U* = 0`. Together with the `U* ≠ 0` check inside `microCMZVerify`, this makes
the identity case contribute nothing to the win probability — the contradiction
O24 derives by coefficient matching, here delivered by the already-proven
`identity_case` (via `toPoly_eq_zero_of_verifPoly_eq_zero`) routed through the
`agmRepr_eval_eq_eval_toPoly` bridge. -/
theorem agm_n1_identity_Ustar_eq_zero (ρU ρV : AGMRepr F 1) (H : G) (x0 xr : F)
    (x : Fin 1 → F) (σStar : G × G) (mStar : F) (tags : List (G × G))
    (msgs : Fin tags.length → F)
    (htag : ∀ j : Fin tags.length,
      (tags.get j).2 = (x0 + xr + msgs j * x 0) • (tags.get j).1)
    (hfresh : ∀ j, mStar ≠ msgs j)
    (hconsistent : ρU.eval (generator G) H (x0 • H) (xr • generator G)
      (fun i => x i • generator G) tags = σStar.1)
    (hverif : AGMPoly.verifPoly msgs mStar (ρU.toReprCoeffs tags.length)
      (ρV.toReprCoeffs tags.length) = 0) :
    σStar.1 = 0 := by
  rw [← hconsistent, agmRepr_eval_eq_eval_toPoly ρU H x0 xr x tags msgs htag,
    AGMPoly.toPoly_eq_zero_of_verifPoly_eq_zero msgs mStar hfresh
      (ρU.toReprCoeffs tags.length) (ρV.toReprCoeffs tags.length) hverif]
  simp

/-! ## The reduction adversary `B₃` -/

/-- The affine-mask point `Var q → F` of the embedding: the fixed-variable masks
`(cη, c0, cXr, cX1)` for `η, x₀, xᵣ, x₁`, together with the per-query `u`-masks
`cu` accumulated in the oracle state. Instantiated once with the `a`-masks and
once with the `b`-masks to give the two `affineSubst` arguments. -/
def embedPoint {q : ℕ} (cη c0 cXr cX1 : F) (cu : Fin q → F) : AGMPoly.Var q → F
  | .eta => cη
  | .x0 => c0
  | .xr => cXr
  | .x1 => cX1
  | .u j => cu j

/-- The oracle state threaded through the reduction: one entry per Sign query
carrying the message vector, the issued tag `(Uⱼ, Vⱼ)`, and the `u`-masks
`(a uⱼ, b uⱼ)` used to build it (needed to assemble the `affineSubst` point on
the forgery). -/
abbrev RedLog (F G : Type) := List ((Fin 1 → F) × (G × G) × F × F)

/-! ## Exponent evaluation (oracle simulation via the 3-DL powers) -/

/-- Evaluate a univariate polynomial of degree `≤ 3` "in the exponent" against
the 3-DL powers `g, X = x·g, X' = x²·g, X'' = x³·g`: returns `(p.eval x) · g`
*without knowing* `x` (see `exponentEval_eq`). The reduction answers
`Verify`/`Help` with this — the represented verification/help equation is a
degree-`≤ 3` polynomial in the challenge exponent. -/
def exponentEval (g X X' X'' : G) (p : Polynomial F) : G :=
  p.coeff 0 • g + p.coeff 1 • X + p.coeff 2 • X' + p.coeff 3 • X''

/-- `exponentEval` against the genuine powers computes `(p.eval x) · g`, for any
`p` of degree `≤ 3`. -/
lemma exponentEval_eq (g : G) (x : F) (p : Polynomial F) (hp : p.natDegree ≤ 3) :
    exponentEval g (x • g) (x ^ 2 • g) (x ^ 3 • g) p = (p.eval x) • g := by
  rw [exponentEval, Polynomial.eval_eq_sum_range' (by omega : p.natDegree < 4)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one, add_smul, smul_smul]

/-- **Reduction `sign` step** (factored out of `reductionOracleImpl` so that reducing the
implementation on a `.sign` query never re-elaborates the `MvPolynomial`/`affineSubst`-heavy
`verify`/`help` branches — the instance-search loop that hangs `evalDist`/`RelTriple` statements
over `reductionOracleImpl (.sign _)` in this `MvPolynomial` import context). Samples the
non-vanishing masks `(au, bu)`, builds the honest tag `(U, V)` with `U = au·g + bu·X`,
`V = key·U` (see `sign_tag_honest`), and appends `(m, (U,V), au, bu)` to the log. -/
noncomputable def reductionSignStep (X X' : G) (a0 aXr aX1 b0 bXr bX1 : F) (m : Fin 1 → F) :
    StateT (RedLog F G) ProbComp (G × G) :=
  StateT.mk fun L => do
      let aubu ← reductionMaskSample X
      let au := aubu.val.1
      let bu := aubu.val.2
      let A := a0 + aXr + m 0 * aX1
      let B := b0 + bXr + m 0 * bX1
      let U := au • generator G + bu • X
      let V := (A * au) • generator G + (A * bu + B * au) • X + (B * bu) • X'
      pure ((U, V), L ++ [(m, (U, V), au, bu)])

/-- **Reduction `verify` step** (factored out; see `reductionSignStep`). -/
noncomputable def reductionVerifyStep (X X' X'' : G) (aEta bEta a0 b0 aXr bXr aX1 bX1 : F)
    (H X0 Xr X1 : G) (m : Fin 1 → F) (σ : G × G) (ρU ρV : AGMRepr F 1) :
    StateT (RedLog F G) ProbComp Bool :=
  StateT.mk fun L =>
      let tags := L.map (fun e => e.2.1)
      let a := embedPoint aEta a0 aXr aX1 (fun j : Fin L.length => (L.get j).2.2.1)
      let b := embedPoint bEta b0 bXr bX1 (fun j : Fin L.length => (L.get j).2.2.2)
      let msgs := fun j : Fin L.length => (L.get j).1 0
      let pU := AGMPoly.affineSubst a b ((ρU.toReprCoeffs L.length).toPoly msgs)
      let keyUniv : Polynomial F :=
        Polynomial.C (a0 + aXr + m 0 * aX1) +
          Polynomial.C (b0 + bXr + m 0 * bX1) * Polynomial.X
      let consistent :=
        ρU.eval (generator G) H X0 Xr (fun _ => X1) tags = σ.1 ∧
        ρV.eval (generator G) H X0 Xr (fun _ => X1) tags = σ.2
      pure (decide consistent && decide (σ.1 ≠ 0) &&
        decide (σ.2 = exponentEval (generator G) X X' X'' (keyUniv * pU)), L)

/-- **Reduction `help` step** (factored out; see `reductionSignStep`). -/
noncomputable def reductionHelpStep (X X' X'' : G) (aEta bEta a0 b0 aXr bXr aX1 bX1 : F)
    (H X0 Xr X1 : G) (A₀ : G) (Av : Fin 1 → G) (Z : G)
    (ρ₀ : AGMRepr F 1) (ρA : Fin 1 → AGMRepr F 1) (ρZ : AGMRepr F 1) :
    StateT (RedLog F G) ProbComp Bool :=
  StateT.mk fun L =>
      let tags := L.map (fun e => e.2.1)
      let a := embedPoint aEta a0 aXr aX1 (fun j : Fin L.length => (L.get j).2.2.1)
      let b := embedPoint bEta b0 bXr bX1 (fun j : Fin L.length => (L.get j).2.2.2)
      let msgs := fun j : Fin L.length => (L.get j).1 0
      let p0 := AGMPoly.affineSubst a b ((ρ₀.toReprCoeffs L.length).toPoly msgs)
      let p1 := AGMPoly.affineSubst a b (((ρA 0).toReprCoeffs L.length).toPoly msgs)
      let keyUniv : Polynomial F :=
        Polynomial.C (a0 + aXr) + Polynomial.C (b0 + bXr) * Polynomial.X
      let x1Univ : Polynomial F :=
        Polynomial.C aX1 + Polynomial.C bX1 * Polynomial.X
      let consistent :=
        ρ₀.eval (generator G) H X0 Xr (fun _ => X1) tags = A₀ ∧
        (∀ i, (ρA i).eval (generator G) H X0 Xr (fun _ => X1) tags = Av i) ∧
        ρZ.eval (generator G) H X0 Xr (fun _ => X1) tags = Z
      pure (decide consistent &&
        decide (Z = exponentEval (generator G) X X' X'' (keyUniv * p0 + x1Univ * p1)), L)

/--
The reduction's **simulated oracle** — answers `A`'s queries with no knowledge of
the secret key `sk`, using only the embedded public elements `(H, X₀, Xᵣ, X₁)`,
the 3-DL powers `(X, X', X'')` over `G₀ = generator G`, and the masks. Each branch
is a thin call to its factored `step` def (`reductionSignStep` / `reductionVerifyStep` /
`reductionHelpStep`) so that reducing the implementation on one constructor never
re-elaborates the others — the `verify`/`help` arms carry `MvPolynomial`/`affineSubst`
terms that loop `SampleableType` instance search in this import context, hanging any
`evalDist`/`RelTriple` statement over `reductionOracleImpl (.sign _)` (see memory
`cmz-probevent-functiontype-hang`). The branch bodies are documented on the step defs.
The masks define the `affineSubst` point via `embedPoint`. -/
noncomputable def reductionOracleImpl (X X' X'' : G)
    (aEta bEta a0 b0 aXr bXr aX1 bX1 : F) (H X0 Xr X1 : G) :
    QueryImpl (AGMOracleSpec F G 1) (StateT (RedLog F G) ProbComp)
  | .sign m => reductionSignStep X X' a0 aXr aX1 b0 bXr bX1 m
  | .verify m σ ρU ρV =>
      reductionVerifyStep X X' X'' aEta bEta a0 b0 aXr bXr aX1 bX1 H X0 Xr X1 m σ ρU ρV
  | .help A₀ Av Z ρ₀ ρA ρZ =>
      reductionHelpStep X X' X'' aEta bEta a0 b0 aXr bXr aX1 bX1 H X0 Xr X1 A₀ Av Z ρ₀ ρA ρZ

/-! ## Root recovery (the reduction's discrete-log extraction step) -/

/--
The reduction's root-finding step. Given the masked univariate polynomial `ψ`
(which vanishes at the challenge exponent `x`, since the forgery satisfies the
verification equation) and the challenge point `X = x • g`, return the root of
`ψ` whose `g`-multiple equals `X`. There is exactly one such root — the discrete
logarithm `x` — so the reduction recovers it after inspecting at most
`deg ψ ≤ 3` candidates.

This is the *honest* extraction: it consults only `ψ.roots` and the decidable
test `r • g = X`; it never uses the noncomputable `glog`. Defaults to `0` when no
root matches (a branch the success analysis rules out). -/
noncomputable def recoverDlog (g X : G) (ψ : Polynomial F) : F :=
  ((ψ.roots.toList).find? (fun r => decide (r • g = X))).getD 0

/--
Correctness of `recoverDlog`: if `ψ` is nonzero and the challenge exponent `x`
is a root of `ψ`, then `recoverDlog g (x • g) ψ = x`. The unique matching root is
`x` itself, by injectivity of `(· • g)` for `g ≠ 0`. -/
lemma recoverDlog_eq {g : G} (hg : g ≠ 0) {x : F} {ψ : Polynomial F}
    (hψ : ψ ≠ 0) (hroot : ψ.IsRoot x) :
    recoverDlog g (x • g) ψ = x := by
  unfold recoverDlog
  have hxmem : x ∈ ψ.roots.toList := by
    rw [Multiset.mem_toList]; exact (Polynomial.mem_roots hψ).mpr hroot
  have hnone : (ψ.roots.toList).find? (fun r => decide (r • g = x • g)) ≠ none := by
    rw [Ne, List.find?_eq_none]; push_neg
    exact ⟨x, hxmem, by simp⟩
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hnone
  rw [hy, Option.getD_some]
  have hpy := List.find?_some hy
  simp only [decide_eq_true_eq] at hpy
  exact smul_left_injective F hg hpy

/--
**Win implies extract (deterministic core).** Suppose the masks `a, b` embed the
challenge so that the verification polynomial of the forgery vanishes at the
embedded point `v ↦ a v + x · b v` (this is the verification equation, O24
Eq. 16, evaluated at the challenge exponent `x`), and the masked univariate
`ψ = affineSubst a b (verifPoly …)` is nonzero. Then the reduction's
root-recovery returns the discrete logarithm `x` of the challenge `X = x · g`.

Combines `eval_affineSubst` (the masked polynomial evaluated at `x` is the
verification equation) with `recoverDlog_eq` (the unique matching root is `x`).
The nonvanishing hypothesis `hne` is the Schwartz–Zippel "good" event, supplied
with probability `≥ 1 − 1/p` at the game layer. -/
lemma recoverDlog_verifPoly_eq {q : ℕ} {a b : AGMPoly.Var q → F} {x : F}
    {msgs : Fin q → F} {mStar : F} {α β : AGMPoly.ReprCoeffs F q}
    (hroot : MvPolynomial.eval (fun v => a v + x * b v)
      (AGMPoly.verifPoly msgs mStar α β) = 0)
    (hne : AGMPoly.affineSubst a b (AGMPoly.verifPoly msgs mStar α β) ≠ 0) :
    recoverDlog (generator G) (x • generator G)
        (AGMPoly.affineSubst a b (AGMPoly.verifPoly msgs mStar α β)) = x := by
  apply recoverDlog_eq generator_ne_zero hne
  rw [Polynomial.IsRoot.def, AGMPoly.eval_affineSubst]
  exact hroot

/--
The **3-DL reduction adversary** for the non-identity branch of O24 Lemma 5.4.
Given the challenge `(g, X = x·g, X' = x²·g, X'' = x³·g)`, it:

1. samples the fixed-variable masks and builds the embedded public parameters
   `H, X₀, Xᵣ, X₁` (O24 Eq. 13);
2. runs `A` against `reductionOracleImpl` (no `sk`), collecting the forgery and
   the final log of issued tags + their `u`-masks;
3. assembles the `affineSubst` point from all masks, forms the masked univariate
   `ψ = affineSubst a b (verifPoly …)`, and returns `recoverDlog g X ψ` — the
   challenge exponent `x`, recovered among `ψ`'s `≤ 3` roots.

Specialized to `g = generator G`: the experiment's group argument is ignored
(`fun _ pows => …`) and `generator G` is used internally. Sound because the
security statements instantiate `qdlAdv 3 (generator G) B₃`, so the supplied `g`
*is* `generator G` and the powers are `x^(i+1) · generator G`. -/
noncomputable def microCMZ3DLReduction (A : AGMUFAdversary F G 1) :
    QDLAdversary 3 F G :=
  fun _ pows => do
    let X := pows 0
    let X' := pows 1
    let X'' := pows 2
    let aEta ← $ᵗ F; let bEta ← $ᵗ F
    let a0 ← $ᵗ F; let b0 ← $ᵗ F
    let aXr ← $ᵗ F; let bXr ← $ᵗ F
    let aX1 ← $ᵗ F; let bX1 ← $ᵗ F
    let H := aEta • generator G + bEta • X
    let X0 := (a0 * aEta) • generator G + (a0 * bEta + b0 * aEta) • X + (b0 * bEta) • X'
    let Xr := aXr • generator G + bXr • X
    let X1 := aX1 • generator G + bX1 • X
    let pp : G × G × (Fin 1 → G) := (X0, Xr, fun _ => X1)
    let ((mStar, _σStar, ρU, ρV), L) ←
      (simulateQ
        (reductionOracleImpl X X' X'' aEta bEta a0 b0 aXr bXr aX1 bX1 H X0 Xr X1)
        (A.run H pp)).run []
    let a := embedPoint aEta a0 aXr aX1 (fun j : Fin L.length => (L.get j).2.2.1)
    let b := embedPoint bEta b0 bXr bX1 (fun j : Fin L.length => (L.get j).2.2.2)
    let msgs := fun j : Fin L.length => (L.get j).1 0
    let ψ := AGMPoly.affineSubst a b
      (AGMPoly.verifPoly msgs (mStar 0)
        (ρU.toReprCoeffs L.length) (ρV.toReprCoeffs L.length))
    pure (recoverDlog (generator G) X ψ)


end KVAC.Schemes.MicroCMZ
