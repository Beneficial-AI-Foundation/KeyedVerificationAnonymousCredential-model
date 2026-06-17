/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.Group
import VCVio

/-!
# μCMZ credential proof relations — Σ-protocols (O24 §5.1, Figure 9)

The keyed-verification credential μCMZ of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §5.1, proves three relations
`R_cmz = R_iu ∪ R_is ∪ R_p` (issuance-user, issuance-server, presentation).
They are built as VCVio `SigmaProtocol` instances, reusing the Schnorr template
(`.lake/packages/VCVio/Examples/Schnorr.lean`) generalized to vectors of
bases/scalars.

All three are generalized-Schnorr Σ-protocols:

- **R_iu** (Eq. 9): the user proves knowledge of `(m⃗, s)` with
  `C' = Σᵢ mᵢ • Xᵢ + s • G`.
- **R_is** (Eq. 10): the issuer proves knowledge of `(x₀, u)` with
  `U' = u • G ∧ X₀ = x₀ • H ∧ V' = x₀ • U' + u • C''`.
- **R_p** (Eq. 11): the user proves knowledge of `(r', r⃗, m⃗)` with
  `(∀ i, Cᵢ = mᵢ • U' + rᵢ • G) ∧ Z = Σᵢ rᵢ • Xᵢ − r' • H`.
  (The `U' ≠ 0` check of Figure 9 is performed by the presentation verifier
  outside the proof, so it is not part of the relation.)

## Design: public bases are parameters

The public bases (`X⃗`, the generator `G`, and `H`) are *parameters* of the
relations (like Schnorr's `g`), not part of the statement. For `R_iu` the
statement is just the commitment `C' : G`; this is what makes `R_iu` total —
every `C'` has a witness — so it admits an honest `GenerableRelation`, whose
`gen_uniform_right` reduces to the single Pedersen-style bijection argument.
`R_is` and `R_p` are *not* total over their statement types (not every tuple
has a witness), so they carry no `GenerableRelation`; none is needed — only
`R_iu` plays the Fiat–Shamir keygen role.

The relations here use the trivial predicate `φ ≡ ⊤`; a non-trivial `φ` would
restrict the witness space and is deferred (it needs a witness-side subtype).

Each protocol comes with `PerfectlyComplete` and `SpeciallySound` proofs, a
transcript simulator, and an `HVZK` proof.

## Elaboration pitfalls (read before editing)

Two classes of nontermination were debugged in this file; avoid reintroducing
them:

1. **Never run `simp`/`rfl` directly on `Pr[…]` goals.** The default simp set
   on probability goals (and kernel `rfl` across `evalDist` boundaries)
   diverges. Drop to computation level first (`congrArg (fun mx => Pr[= t |
   mx])`, or rewrite the computation with a `have`), or use the targeted
   helpers below (`probOutput_decide_bind₃/₄`, `probOutput_eq_one_iff`).
2. **Never let instance search synthesize `SampleableType`/`Inhabited` for
   product types from scratch.** The `Inhabited` side-goal search diverges
   through the algebraic instance graph (`Module`/`Subsingleton` paths). The
   needed product instance is registered locally below with the `Inhabited`
   arguments supplied explicitly; sample product announcements componentwise
   (`do let a ← $ᵗ _; …`) instead of `$ᵗ (… × …)`.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open OracleSpec OracleComp SigmaProtocol KVAC.Core ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-- `SampleableType` for the witness type of `R_iu`. Synthesizing this through
VCVio's generic product instance diverges in this file's algebraic context
(the `Inhabited` side-goal search does not terminate), so it is provided once,
with the `Inhabited` arguments supplied explicitly. -/
private local instance (priority := high) : Inhabited F := ⟨0⟩


/-! ## Perfect-completeness helpers

The `PerfectlyComplete` goals below are probability-one statements about
computations that sample a few uniforms and `return` a `decide`. Rather than
unfolding the probability semantics with `simp` (which does not terminate on
the function-type samples used here), these helpers reduce the goal to the
underlying universally-true Boolean via `probOutput_eq_one_iff`
(no failure + support is exactly `{true}`). -/

private lemma probOutput_decide_bind₃ {α β γ : Type}
    [SampleableType α] [SampleableType β] [SampleableType γ]
    [Nonempty α] [Nonempty β] [Nonempty γ]
    (p : α → β → γ → Bool) (hp : ∀ a b c, p a b c = true) :
    Pr[= true | (do
      let a ← $ᵗ α
      let b ← $ᵗ β
      let c ← $ᵗ γ
      pure (p a b c) : ProbComp Bool)] = 1 := by
  rw [probOutput_eq_one_iff]
  constructor
  · simp
  · ext b'
    simp only [support_bind, support_uniformSample, support_pure,
      Set.mem_iUnion, Set.mem_univ, Set.iUnion_true, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, b, c, rfl⟩
      exact hp a b c
    · intro hb'
      obtain ⟨a⟩ := ‹Nonempty α›
      obtain ⟨b⟩ := ‹Nonempty β›
      obtain ⟨c⟩ := ‹Nonempty γ›
      exact ⟨a, b, c, by rw [hb', hp]⟩

/-- Four-sample version of `probOutput_decide_bind₃`. -/
private lemma probOutput_decide_bind₄ {α β γ δ : Type}
    [SampleableType α] [SampleableType β] [SampleableType γ] [SampleableType δ]
    [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ]
    (p : α → β → γ → δ → Bool) (hp : ∀ a b c d, p a b c d = true) :
    Pr[= true | (do
      let a ← $ᵗ α
      let b ← $ᵗ β
      let c ← $ᵗ γ
      let d ← $ᵗ δ
      pure (p a b c d) : ProbComp Bool)] = 1 := by
  rw [probOutput_eq_one_iff]
  constructor
  · simp
  · ext b'
    simp only [support_bind, support_uniformSample, support_pure,
      Set.mem_iUnion, Set.mem_univ, Set.iUnion_true, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, b, c, d, rfl⟩
      exact hp a b c d
    · intro hb'
      obtain ⟨a⟩ := ‹Nonempty α›
      obtain ⟨b⟩ := ‹Nonempty β›
      obtain ⟨c⟩ := ‹Nonempty γ›
      obtain ⟨d⟩ := ‹Nonempty δ›
      exact ⟨a, b, c, d, by rw [hb', hp]⟩

/-- Congruence under a uniform bind: if the continuations agree pointwise on the
output probability, the bound computations do too. -/
private lemma probOutput_bind_uniform_congr {A γ : Type} [SampleableType A]
    {k₁ k₂ : A → ProbComp γ} {t : γ} (h : ∀ a, Pr[=t | k₁ a] = Pr[=t | k₂ a]) :
    Pr[=t | (($ᵗ A : ProbComp A) >>= k₁)] = Pr[=t | (($ᵗ A : ProbComp A) >>= k₂)] := by
  rw [probOutput_bind_eq_tsum ($ᵗ A) k₁ t, probOutput_bind_eq_tsum ($ᵗ A) k₂ t]
  exact tsum_congr fun a => by rw [h a]

/-! ## R_iu — issuance user proof (O24 Eq. 9) -/

/-- The R_iu relation (O24 Fig 9, issuance user proof, with `φ ≡ ⊤`):
the statement `C'` together with the public bases `X⃗`, `G` is satisfied by the
witness `(m⃗, s)` iff `C' = Σᵢ mᵢ • Xᵢ + s • gen`. -/
def riuRel (gen : G) (X : Fin n → G) : G → ((Fin n → F) × F) → Bool :=
  fun Cp w => decide (Cp = (∑ i, w.1 i • X i) + w.2 • gen)

/-- R_iu as a Σ-protocol (a generalized Schnorr proof of knowledge of a
representation of `C'` in the bases `X⃗, G`). The public commitment is the
announcement `R`; the challenge is a full-field scalar; the response is the
masked witness `(z⃗ₘ, zₛ)`. -/
def riuSigma (gen : G) (X : Fin n → G) :
    SigmaProtocol G ((Fin n → F) × F) G ((Fin n → F) × F) F ((Fin n → F) × F)
      (riuRel gen X) where
  commit _Cp _w := do
    let ρ ← $ᵗ (Fin n → F)
    let ρs ← $ᵗ F
    return ((∑ i, ρ i • X i) + ρs • gen, (ρ, ρs))
  respond _Cp w sc c := pure (fun i => sc.1 i + c * w.1 i, sc.2 + c * w.2)
  verify _Cp R c z := decide ((∑ i, z.1 i • X i) + z.2 • gen = R + c • _Cp)
  sim _Cp := $ᵗ G
  extract c₁ z₁ c₂ z₂ :=
    pure (fun i => (z₁.1 i - z₂.1 i) * (c₁ - c₂)⁻¹, (z₁.2 - z₂.2) * (c₁ - c₂)⁻¹)

/-- Completeness of the R_iu Σ-protocol: an honest prover with a valid witness
always convinces the verifier. Pure `Module` algebra (`add_smul`, `mul_smul`). -/
theorem riuSigma_complete (gen : G) (X : Fin n → G) :
    PerfectlyComplete (riuSigma (F := F) gen X) := by
  intro Cp w h
  have h_eq : Cp = (∑ i, w.1 i • X i) + w.2 • gen := of_decide_eq_true h
  simp only [riuSigma, bind_assoc, pure_bind]
  have hverify : ∀ (ρ : Fin n → F) (ρs c : F),
      (∑ i, (ρ i + c * w.1 i) • X i) + (ρs + c * w.2) • gen
        = ((∑ i, ρ i • X i) + ρs • gen) + c • Cp := by
    intro ρ ρs c
    rw [h_eq]
    simp only [add_smul, mul_smul, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
    abel
  exact probOutput_decide_bind₃ _ fun ρ ρs c => decide_eq_true (hverify ρ ρs c)

/-- Special soundness of the R_iu Σ-protocol: two accepting transcripts with
the same announcement and distinct challenges yield a valid witness via the
`extract` field. -/
theorem riuSigma_speciallySound (gen : G) (X : Fin n → G) :
    SpeciallySound (riuSigma (F := F) gen X) := by
  intro Cp R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [riuSigma] at *
  simp only [support_pure, Set.mem_singleton_iff] at h_w
  subst h_w
  simp only [decide_eq_true_eq] at h_v1 h_v2
  simp only [riuRel, decide_eq_true_eq]
  have h_ne' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have h_sub : (∑ i, (z₁.1 i - z₂.1 i) • X i) + (z₁.2 - z₂.2) • gen
      = (c₁ - c₂) • Cp := by
    calc (∑ i, (z₁.1 i - z₂.1 i) • X i) + (z₁.2 - z₂.2) • gen
        = ((∑ i, z₁.1 i • X i) + z₁.2 • gen)
            - ((∑ i, z₂.1 i • X i) + z₂.2 • gen) := by
          simp only [sub_smul, Finset.sum_sub_distrib]; abel
      _ = (R + c₁ • Cp) - (R + c₂ • Cp) := by rw [h_v1, h_v2]
      _ = (c₁ - c₂) • Cp := by rw [sub_smul]; abel
  calc Cp = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • Cp) := by
        rw [← mul_smul, inv_mul_cancel₀ h_ne', one_smul]
    _ = (c₁ - c₂)⁻¹ • ((∑ i, (z₁.1 i - z₂.1 i) • X i) + (z₁.2 - z₂.2) • gen) := by
        rw [h_sub]
    _ = (∑ i, ((z₁.1 i - z₂.1 i) * (c₁ - c₂)⁻¹) • X i)
          + ((z₁.2 - z₂.2) * (c₁ - c₂)⁻¹) • gen := by
        simp only [smul_add, Finset.smul_sum, ← mul_smul]
        simp only [mul_comm]

/-- Transcript simulator for the R_iu Σ-protocol: sample the challenge and the
response uniformly and solve the verification equation for the announcement,
`R := (∑ᵢ zᵢ • Xᵢ) + zₛ • gen − c • C'`. -/
noncomputable def riuSimTranscript (gen : G) (X : Fin n → G) (Cp : G) :
    ProbComp (G × F × ((Fin n → F) × F)) := do
  let c ← $ᵗ F
  let zm ← $ᵗ (Fin n → F)
  let zs ← $ᵗ F
  return ((∑ i, zm i • X i) + zs • gen - c • Cp, c, (zm, zs))

/-- The simulated-transcript value of `riuSigma` on responses `(a, b)` and
challenge `c`: the announcement is solved from the verification equation. -/
private def svfun (gen : G) (X : Fin n → G) (Cp : G)
    (a : Fin n → F) (b c : F) : G × F × (Fin n → F) × F :=
  ((∑ i, a i • X i) + b • gen - c • Cp, c, a, b)

/-- Honest-verifier zero-knowledge of the R_iu Σ-protocol (O24 Eq. 9): real
transcripts are distributed exactly as `riuSimTranscript`. -/
theorem riuSigma_hvzk (gen : G) (X : Fin n → G) :
    HVZK (riuSigma (F := F) gen X) (riuSimTranscript gen X) := by
  intro Cp w hrel
  have h_eq : Cp = (∑ i, w.1 i • X i) + w.2 • gen := of_decide_eq_true hrel
  simp only [riuSigma, riuSimTranscript, bind_assoc, pure_bind]
  apply evalDist_ext; intro t
  -- 1. Bring the challenge to the front (TWO swaps: a single `vcstep rw` would
  --    swap the two masks `ρ, ρs` and peel the wrong sample), then peel it.
  vcstep rw under 1
  vcstep rw
  vcstep rw congr' as ⟨c⟩
  -- 2. For fixed `c`, rewrite the real value to the simulated value with each mask
  --    shifted by the challenge-scaled witness, then strip the two shifts.
  have hbody : ∀ (ρ : Fin n → F) (ρs : F),
      ((∑ i, ρ i • X i) + ρs • gen, c, (fun i => ρ i + c * w.1 i), ρs + c * w.2)
        = svfun gen X Cp ((fun j => c * w.1 j) + ρ) (c * w.2 + ρs) c := by
    intro ρ ρs
    have e1 : (∑ i, ρ i • X i) + ρs • gen
        = (∑ i, ((fun j => c * w.1 j) + ρ) i • X i) + (c * w.2 + ρs) • gen - c • Cp := by
      rw [h_eq]
      simp only [Pi.add_apply, add_smul, mul_smul, smul_add, Finset.smul_sum,
        Finset.sum_add_distrib]
      abel
    have e3 : (fun i => ρ i + c * w.1 i) = (fun j => c * w.1 j) + ρ := by
      funext i; simp only [Pi.add_apply]; ring
    simp only [svfun, e1, e3, add_comm ρs (c * w.2)]
  simp only [hbody]
  refine (probOutput_bind_add_left_uniform (α := Fin n → F) (m := fun j => c * w.1 j)
    (f := fun ρ => ($ᵗ F : ProbComp F) >>= fun ρs => pure (svfun gen X Cp ρ (c * w.2 + ρs) c))
    (z := t)).trans ?_
  refine probOutput_bind_uniform_congr fun ρ => ?_
  exact probOutput_bind_add_left_uniform (α := F) (m := c * w.2)
    (f := fun ρs => pure (svfun gen X Cp ρ ρs c)) (z := t)

/-! ## R_iu as a generable relation -/
/-- Unfolding of product uniform sampling: VCVio's `SampleableType (α × β)`
instance samples the components independently. Stated as a computation-level
equality so proofs can `rw` with it instead of forcing the kernel to check the
(very expensive) definitional equality between the instance's `seq` form and a
`bind` chain. -/
private lemma uniformSample_prod_eq {α β : Type} [Fintype α] [Fintype β]
    [Inhabited α] [Inhabited β] [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b)) := by
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β) : ProbComp (α × β)) = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

/-- The honest statement–witness generator for `R_iu`: sample `(m⃗, s)`
uniformly and set `C' = Σᵢ mᵢ • Xᵢ + s • gen`. Lifted out of the
`GenerableRelation` structure so the lemmas below are about a plain constant. -/
private noncomputable def riuGenComp (gen : G) (X : Fin n → G) :
    ProbComp (G × ((Fin n → F) × F)) := do
  let m ← $ᵗ (Fin n → F)
  let s ← $ᵗ F
  return ((∑ i, m i • X i) + s • gen, (m, s))

private lemma riuGenComp_sound (gen : G) (X : Fin n → G) (y : G)
    (w : (Fin n → F) × F) (h : (y, w) ∈ support (riuGenComp (F := F) gen X)) :
    riuRel gen X y w = true := by
  simp only [riuGenComp, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ,
    exists_true_left] at h
  obtain ⟨m, s, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  simp only [riuRel, decide_eq_true_eq]

private lemma riuGenComp_uniform_left (gen : G) (X : Fin n → G)
    (w : (Fin n → F) × F) :
    Pr[= w | Prod.snd <$> riuGenComp (F := F) gen X] =
      Pr[= w | ($ᵗ ((Fin n → F) × F) : ProbComp _)] := by
  rw [uniformSample_prod_eq]
  refine congrArg (fun mx => Pr[= w | mx]) ?_
  simp only [riuGenComp, map_bind, map_pure]

private lemma riuGenComp_uniform_right (gen : G) (X : Fin n → G)
    (hgen : Function.Bijective (· • gen : F → G)) (x : G) :
    Pr[= x | Prod.fst <$> riuGenComp (F := F) gen X] =
      Pr[= x | ($ᵗ G : ProbComp G)] := by
  have hcomp : Prod.fst <$> riuGenComp (F := F) gen X
      = (do
        let m ← $ᵗ (Fin n → F)
        let s ← $ᵗ F
        pure ((∑ i, m i • X i) + s • gen) : ProbComp G) := by
    simp only [riuGenComp, map_bind, map_pure]
  rw [hcomp]
  have hconst : ∀ m : Fin n → F,
      m ∈ support ($ᵗ (Fin n → F) : ProbComp (Fin n → F)) →
      Pr[= x | (do let s ← $ᵗ F; pure ((∑ i, m i • X i) + s • gen) : ProbComp G)]
        = Pr[= x | ($ᵗ G : ProbComp G)] := by
    intro m _
    have key := probOutput_bind_bijective_uniform_cross (α := F)
      (fun s : F => s • gen) hgen (fun y : G => pure ((∑ i, m i • X i) + y)) x
    have hadd := probOutput_add_left_uniform (α := G) (∑ i, m i • X i) x
    rw [map_eq_bind_pure_comp] at hadd
    simp only [Function.comp_def] at hadd
    exact key.trans hadd
  rw [probOutput_bind_of_const _ hconst, probFailure_uniformSample, tsub_zero,
    one_mul]

/-- R_iu is a generable relation: sample `(m⃗, s)` uniformly and set
`C' = Σᵢ mᵢ • Xᵢ + s • gen`. Requires `· • gen` to be a bijection `F → G` (true
when `gen` generates a prime-order group with `|F| = |G|`); carried as a
hypothesis here, exactly as VCVio's Pedersen development does.

The fields are standalone private lemmas (about the lifted-out generator
`riuGenComp`) assembled by plain term application — running tactics inside
this dependent structure's fields does not terminate. -/
noncomputable def riuGen (gen : G) (X : Fin n → G)
    (hgen : Function.Bijective (· • gen : F → G)) :
    GenerableRelation G ((Fin n → F) × F) (riuRel gen X) where
  gen := riuGenComp gen X
  gen_sound := riuGenComp_sound gen X
  gen_uniform_left := riuGenComp_uniform_left gen X
  gen_uniform_right := riuGenComp_uniform_right gen X hgen

/-! ## R_is — issuance server proof (O24 Eq. 10) -/

/-- The R_is relation (O24 Fig 9, issuance server proof): the statement
`(X₀, C'', U', V')` is satisfied by the witness `(x₀, u)` iff
`U' = u • gen ∧ X₀ = x₀ • H ∧ V' = x₀ • U' + u • C''`. -/
def risRel (gen H : G) : (G × G × G × G) → (F × F) → Bool :=
  fun s w => decide
    (s.2.2.1 = w.2 • gen ∧ s.1 = w.1 • H ∧
      s.2.2.2 = w.1 • s.2.2.1 + w.2 • s.2.1)

/-- R_is as a Σ-protocol: a three-equation AND-composition Schnorr proof over
the bases `gen`, `H`, and the statement-dependent bases `U'`, `C''`. The
announcement is one group element per equation; the response is the masked
witness `(z_x, z_u)`. -/
def risSigma (gen H : G) :
    SigmaProtocol (G × G × G × G) (F × F) (G × G × G) (F × F) F (F × F)
      (risRel gen H) where
  commit s _w := do
    let ρx ← $ᵗ F
    let ρu ← $ᵗ F
    return ((ρu • gen, ρx • H, ρx • s.2.2.1 + ρu • s.2.1), (ρx, ρu))
  respond _s w sc c := pure (sc.1 + c * w.1, sc.2 + c * w.2)
  verify s R c z := decide
    (z.2 • gen = R.1 + c • s.2.2.1 ∧
      z.1 • H = R.2.1 + c • s.1 ∧
      z.1 • s.2.2.1 + z.2 • s.2.1 = R.2.2 + c • s.2.2.2)
  sim _s := do
    let a ← $ᵗ G
    let b ← $ᵗ G
    let c ← $ᵗ G
    pure (a, b, c)
  extract c₁ z₁ c₂ z₂ :=
    pure ((z₁.1 - z₂.1) * (c₁ - c₂)⁻¹, (z₁.2 - z₂.2) * (c₁ - c₂)⁻¹)

/-- Completeness of the R_is Σ-protocol. -/
theorem risSigma_complete (gen H : G) :
    PerfectlyComplete (risSigma (F := F) gen H) := by
  intro s w h
  obtain ⟨hU, hX, hV⟩ := of_decide_eq_true h
  simp only [risSigma, bind_assoc, pure_bind]
  have h1 : ∀ (ρu c : F), (ρu + c * w.2) • gen = ρu • gen + c • s.2.2.1 := by
    intro ρu c; rw [add_smul, mul_smul, ← hU]
  have h2 : ∀ (ρx c : F), (ρx + c * w.1) • H = ρx • H + c • s.1 := by
    intro ρx c; rw [add_smul, mul_smul, ← hX]
  have h3 : ∀ (ρx ρu c : F),
      (ρx + c * w.1) • s.2.2.1 + (ρu + c * w.2) • s.2.1
        = (ρx • s.2.2.1 + ρu • s.2.1) + c • s.2.2.2 := by
    intro ρx ρu c
    rw [hV]
    simp only [add_smul, mul_smul, smul_add]
    abel
  exact probOutput_decide_bind₃ _ fun ρx ρu c =>
    decide_eq_true ⟨h1 ρu c, h2 ρx c, h3 ρx ρu c⟩

/-- Special soundness of the R_is Σ-protocol. -/
theorem risSigma_speciallySound (gen H : G) :
    SpeciallySound (risSigma (F := F) gen H) := by
  intro s R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [risSigma] at *
  simp only [support_pure, Set.mem_singleton_iff] at h_w
  subst h_w
  simp only [decide_eq_true_eq] at h_v1 h_v2
  obtain ⟨h1U, h1X, h1V⟩ := h_v1
  obtain ⟨h2U, h2X, h2V⟩ := h_v2
  simp only [risRel, decide_eq_true_eq]
  have h_ne' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have hdiv : ∀ (a : F) (A B : G), (c₁ - c₂) • B = a • A →
      B = (a * (c₁ - c₂)⁻¹) • A := by
    intro a A B hab
    calc B = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • B) := by
          rw [← mul_smul, inv_mul_cancel₀ h_ne', one_smul]
      _ = (c₁ - c₂)⁻¹ • (a • A) := by rw [hab]
      _ = (a * (c₁ - c₂)⁻¹) • A := by rw [← mul_smul, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · -- U' = ((z₁.2 - z₂.2) * (c₁ - c₂)⁻¹) • gen
    refine hdiv _ _ _ ?_
    calc (c₁ - c₂) • s.2.2.1
        = (z₁.2 • gen) - (z₂.2 • gen) := by rw [h1U, h2U, sub_smul]; abel
      _ = (z₁.2 - z₂.2) • gen := by rw [sub_smul]
  · -- X₀ = ((z₁.1 - z₂.1) * (c₁ - c₂)⁻¹) • H
    refine hdiv _ _ _ ?_
    calc (c₁ - c₂) • s.1
        = (z₁.1 • H) - (z₂.1 • H) := by rw [h1X, h2X, sub_smul]; abel
      _ = (z₁.1 - z₂.1) • H := by rw [sub_smul]
  · -- V' = wx • U' + wu • C''
    have h_sub : (c₁ - c₂) • s.2.2.2
        = (z₁.1 - z₂.1) • s.2.2.1 + (z₁.2 - z₂.2) • s.2.1 := by
      calc (c₁ - c₂) • s.2.2.2
          = (z₁.1 • s.2.2.1 + z₁.2 • s.2.1)
              - (z₂.1 • s.2.2.1 + z₂.2 • s.2.1) := by
            rw [h1V, h2V, sub_smul]; abel
        _ = (z₁.1 - z₂.1) • s.2.2.1 + (z₁.2 - z₂.2) • s.2.1 := by
            simp only [sub_smul]; abel
    calc s.2.2.2
        = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • s.2.2.2) := by
          rw [← mul_smul, inv_mul_cancel₀ h_ne', one_smul]
      _ = (c₁ - c₂)⁻¹ • ((z₁.1 - z₂.1) • s.2.2.1 + (z₁.2 - z₂.2) • s.2.1) := by
          rw [h_sub]
      _ = ((z₁.1 - z₂.1) * (c₁ - c₂)⁻¹) • s.2.2.1
            + ((z₁.2 - z₂.2) * (c₁ - c₂)⁻¹) • s.2.1 := by
          simp only [smul_add, ← mul_smul]
          simp only [mul_comm]

/-- Transcript simulator for the R_is Σ-protocol: sample the challenge and the
response uniformly and solve the three verification equations for the
announcements. -/
noncomputable def risSimTranscript (gen H : G) (s : G × G × G × G) :
    ProbComp ((G × G × G) × F × (F × F)) := do
  let c ← $ᵗ F
  let zx ← $ᵗ F
  let zu ← $ᵗ F
  return ((zu • gen - c • s.2.2.1, zx • H - c • s.1,
    zx • s.2.2.1 + zu • s.2.1 - c • s.2.2.2), c, (zx, zu))

/-- The simulated-transcript value of `risSigma` on responses `(a, b) = (zx, zu)`
and challenge `c`: the three announcements are solved from the verification
equations. The statement is `s = (X₀, C'', U', V')`. -/
private def svfunRis (gen H : G) (s : G × G × G × G) (a b c : F) :
    (G × G × G) × F × (F × F) :=
  ((b • gen - c • s.2.2.1, a • H - c • s.1, a • s.2.2.1 + b • s.2.1 - c • s.2.2.2), c, (a, b))

/-- Honest-verifier zero-knowledge of the R_is Σ-protocol (O24 Eq. 10). Same
shape as `riuSigma_hvzk`: reorder the challenge to the front, rewrite the real
announcement to the simulated one with each mask shifted by the challenge-scaled
witness, then strip the two shifts. Both masks are scalars here, so both shifts
are over `F`. -/
theorem risSigma_hvzk (gen H : G) :
    HVZK (risSigma (F := F) gen H) (risSimTranscript gen H) := by
  intro s w hrel
  obtain ⟨hU, hX, hV⟩ := of_decide_eq_true hrel
  simp only [risSigma, risSimTranscript, bind_assoc, pure_bind]
  apply evalDist_ext; intro t
  vcstep rw under 1
  vcstep rw
  vcstep rw congr' as ⟨c⟩
  have hbody : ∀ (ρx ρu : F),
      ((ρu • gen, ρx • H, ρx • s.2.2.1 + ρu • s.2.1), c, (ρx + c * w.1, ρu + c * w.2))
        = svfunRis gen H s (c * w.1 + ρx) (c * w.2 + ρu) c := by
    intro ρx ρu
    have e1 : ρu • gen = (c * w.2 + ρu) • gen - c • s.2.2.1 := by
      rw [hU]; simp only [add_smul, mul_smul]; abel
    have e2 : ρx • H = (c * w.1 + ρx) • H - c • s.1 := by
      rw [hX]; simp only [add_smul, mul_smul]; abel
    have e3 : ρx • s.2.2.1 + ρu • s.2.1
        = (c * w.1 + ρx) • s.2.2.1 + (c * w.2 + ρu) • s.2.1 - c • s.2.2.2 := by
      rw [hV]; simp only [add_smul, mul_smul, smul_add]; abel
    simp only [svfunRis, e1, e2, e3, add_comm ρx (c * w.1), add_comm ρu (c * w.2)]
  simp only [hbody]
  refine (probOutput_bind_add_left_uniform (α := F) (m := c * w.1)
    (f := fun ρx => ($ᵗ F : ProbComp F) >>= fun ρu =>
      pure (svfunRis gen H s ρx (c * w.2 + ρu) c)) (z := t)).trans ?_
  refine probOutput_bind_uniform_congr fun ρx => ?_
  exact probOutput_bind_add_left_uniform (α := F) (m := c * w.2)
    (f := fun ρu => pure (svfunRis gen H s ρx ρu c)) (z := t)

/-! ## R_p — presentation proof (O24 Eq. 11) -/

/-- The R_p relation (O24 Fig 9, presentation proof, with `φ ≡ ⊤`): the
statement `(U', C⃗, Z)` together with the public bases `X⃗`, `gen`, `H` is
satisfied by the witness `(r', r⃗, m⃗)` iff
`(∀ i, Cᵢ = mᵢ • U' + rᵢ • gen) ∧ Z = Σᵢ rᵢ • Xᵢ − r' • H`. -/
def rpRel (gen H : G) (X : Fin n → G) :
    (G × (Fin n → G) × G) → (F × (Fin n → F) × (Fin n → F)) → Bool :=
  fun s w => decide
    ((∀ i, s.2.1 i = w.2.2 i • s.1 + w.2.1 i • gen) ∧
      s.2.2 = (∑ i, w.2.1 i • X i) - w.1 • H)

/-- R_p as a Σ-protocol: `n` opening equations for the commitments `Cᵢ` (over
the statement-dependent base `U'` and `gen`) AND one equation for `Z` (over
`X⃗` and `H`). The announcement is one group element per equation; the response
is the masked witness `(z_{r'}, z⃗_r, z⃗_m)`. -/
def rpSigma (gen H : G) (X : Fin n → G) :
    SigmaProtocol (G × (Fin n → G) × G) (F × (Fin n → F) × (Fin n → F))
      ((Fin n → G) × G) (F × (Fin n → F) × (Fin n → F)) F
      (F × (Fin n → F) × (Fin n → F)) (rpRel gen H X) where
  commit s _w := do
    let ρr' ← $ᵗ F
    let ρr ← $ᵗ (Fin n → F)
    let ρm ← $ᵗ (Fin n → F)
    return ((fun i => ρm i • s.1 + ρr i • gen, (∑ i, ρr i • X i) - ρr' • H),
      (ρr', ρr, ρm))
  respond _s w sc c := pure
    (sc.1 + c * w.1, fun i => sc.2.1 i + c * w.2.1 i,
      fun i => sc.2.2 i + c * w.2.2 i)
  verify s R c z := decide
    ((∀ i, z.2.2 i • s.1 + z.2.1 i • gen = R.1 i + c • s.2.1 i) ∧
      (∑ i, z.2.1 i • X i) - z.1 • H = R.2 + c • s.2.2)
  sim _s := do
    let a ← $ᵗ (Fin n → G)
    let b ← $ᵗ G
    pure (a, b)
  extract c₁ z₁ c₂ z₂ := pure
    ((z₁.1 - z₂.1) * (c₁ - c₂)⁻¹,
      fun i => (z₁.2.1 i - z₂.2.1 i) * (c₁ - c₂)⁻¹,
      fun i => (z₁.2.2 i - z₂.2.2 i) * (c₁ - c₂)⁻¹)

/-- Completeness of the R_p Σ-protocol. -/
theorem rpSigma_complete (gen H : G) (X : Fin n → G) :
    PerfectlyComplete (rpSigma (F := F) gen H X) := by
  intro s w h
  obtain ⟨hC, hZ⟩ := of_decide_eq_true h
  simp only [rpSigma, bind_assoc, pure_bind]
  have h1 : ∀ (ρm ρr : Fin n → F) (c : F) (i : Fin n),
      (ρm i + c * w.2.2 i) • s.1 + (ρr i + c * w.2.1 i) • gen
        = (ρm i • s.1 + ρr i • gen) + c • s.2.1 i := by
    intro ρm ρr c i
    rw [hC i]
    simp only [add_smul, mul_smul, smul_add]
    abel
  have h2 : ∀ (ρr : Fin n → F) (ρr' c : F),
      (∑ i, (ρr i + c * w.2.1 i) • X i) - (ρr' + c * w.1) • H
        = ((∑ i, ρr i • X i) - ρr' • H) + c • s.2.2 := by
    intro ρr ρr' c
    rw [hZ]
    simp only [add_smul, mul_smul, smul_sub, Finset.smul_sum,
      Finset.sum_add_distrib]
    abel
  exact probOutput_decide_bind₄ _ fun ρr' ρr ρm c =>
    decide_eq_true ⟨fun i => h1 ρm ρr c i, h2 ρr ρr' c⟩

/-- Special soundness of the R_p Σ-protocol. -/
theorem rpSigma_speciallySound (gen H : G) (X : Fin n → G) :
    SpeciallySound (rpSigma (F := F) gen H X) := by
  intro s R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [rpSigma] at *
  simp only [support_pure, Set.mem_singleton_iff] at h_w
  subst h_w
  simp only [decide_eq_true_eq] at h_v1 h_v2
  obtain ⟨h1C, h1Z⟩ := h_v1
  obtain ⟨h2C, h2Z⟩ := h_v2
  simp only [rpRel, decide_eq_true_eq]
  have h_ne' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have hcancel : ∀ B : G, (c₁ - c₂)⁻¹ • ((c₁ - c₂) • B) = B := by
    intro B; rw [← mul_smul, inv_mul_cancel₀ h_ne', one_smul]
  refine ⟨?_, ?_⟩
  · -- per-commitment openings
    intro i
    have h_sub : (c₁ - c₂) • s.2.1 i
        = (z₁.2.2 i - z₂.2.2 i) • s.1 + (z₁.2.1 i - z₂.2.1 i) • gen := by
      calc (c₁ - c₂) • s.2.1 i
          = (z₁.2.2 i • s.1 + z₁.2.1 i • gen)
              - (z₂.2.2 i • s.1 + z₂.2.1 i • gen) := by
            rw [h1C i, h2C i, sub_smul]; abel
        _ = (z₁.2.2 i - z₂.2.2 i) • s.1 + (z₁.2.1 i - z₂.2.1 i) • gen := by
            simp only [sub_smul]; abel
    calc s.2.1 i
        = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • s.2.1 i) := (hcancel _).symm
      _ = (c₁ - c₂)⁻¹ • ((z₁.2.2 i - z₂.2.2 i) • s.1
            + (z₁.2.1 i - z₂.2.1 i) • gen) := by rw [h_sub]
      _ = ((z₁.2.2 i - z₂.2.2 i) * (c₁ - c₂)⁻¹) • s.1
            + ((z₁.2.1 i - z₂.2.1 i) * (c₁ - c₂)⁻¹) • gen := by
          simp only [smul_add, ← mul_smul]
          simp only [mul_comm]
  · -- the Z equation
    have h_sub : (c₁ - c₂) • s.2.2
        = (∑ i, (z₁.2.1 i - z₂.2.1 i) • X i) - (z₁.1 - z₂.1) • H := by
      calc (c₁ - c₂) • s.2.2
          = ((∑ i, z₁.2.1 i • X i) - z₁.1 • H)
              - ((∑ i, z₂.2.1 i • X i) - z₂.1 • H) := by
            rw [h1Z, h2Z, sub_smul]; abel
        _ = (∑ i, (z₁.2.1 i - z₂.2.1 i) • X i) - (z₁.1 - z₂.1) • H := by
            simp only [sub_smul, Finset.sum_sub_distrib]; abel
    calc s.2.2
        = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • s.2.2) := (hcancel _).symm
      _ = (c₁ - c₂)⁻¹ • ((∑ i, (z₁.2.1 i - z₂.2.1 i) • X i)
            - (z₁.1 - z₂.1) • H) := by rw [h_sub]
      _ = (∑ i, ((z₁.2.1 i - z₂.2.1 i) * (c₁ - c₂)⁻¹) • X i)
            - ((z₁.1 - z₂.1) * (c₁ - c₂)⁻¹) • H := by
          simp only [smul_sub, Finset.smul_sum, ← mul_smul]
          simp only [mul_comm]

/-- Transcript simulator for the R_p Σ-protocol: sample the challenge and the
response uniformly and solve the `n + 1` verification equations for the
announcements. -/
noncomputable def rpSimTranscript (gen H : G) (X : Fin n → G)
    (s : G × (Fin n → G) × G) :
    ProbComp (((Fin n → G) × G) × F × (F × (Fin n → F) × (Fin n → F))) := do
  let c ← $ᵗ F
  let zr' ← $ᵗ F
  let zr ← $ᵗ (Fin n → F)
  let zm ← $ᵗ (Fin n → F)
  return ((fun i => zm i • s.1 + zr i • gen - c • s.2.1 i,
    (∑ i, zr i • X i) - zr' • H - c • s.2.2), c, (zr', zr, zm))

/-- The simulated-transcript value of `rpSigma` on responses `(a, b, d) = (z_{r'}, z⃗_r, z⃗_m)`
and challenge `c`: the `n` opening announcements and the `Z`-announcement are solved
from the verification equations. The statement is `s = (U', C⃗, Z)`. -/
private def svfunRp (gen H : G) (X : Fin n → G) (s : G × (Fin n → G) × G)
    (a : F) (b d : Fin n → F) (c : F) :
    ((Fin n → G) × G) × F × (F × (Fin n → F) × (Fin n → F)) :=
  ((fun i => d i • s.1 + b i • gen - c • s.2.1 i, (∑ i, b i • X i) - a • H - c • s.2.2),
    c, (a, b, d))

/-- Honest-verifier zero-knowledge of the R_p Σ-protocol (O24 Eq. 11). Same shape
as before, scaled to three masks: a scalar `ρr'` and two vector masks `ρr, ρm`,
with an `n`-opening + one-`Z` announcement. Reorder the challenge to the front
(three swaps), rewrite to the simulated value with each mask shifted, then strip
the three shifts (one over `F`, two over `Fin n → F`). -/
theorem rpSigma_hvzk (gen H : G) (X : Fin n → G) :
    HVZK (rpSigma (F := F) gen H X) (rpSimTranscript gen H X) := by
  intro s w hrel
  obtain ⟨hC, hZ⟩ := of_decide_eq_true hrel
  simp only [rpSigma, rpSimTranscript, bind_assoc, pure_bind]
  apply evalDist_ext; intro t
  vcstep rw under 2
  vcstep rw under 1
  vcstep rw
  vcstep rw congr' as ⟨c⟩
  have hbody : ∀ (ρr' : F) (ρr ρm : Fin n → F),
      ((fun i => ρm i • s.1 + ρr i • gen, (∑ i, ρr i • X i) - ρr' • H), c,
       (ρr' + c * w.1, fun i => ρr i + c * w.2.1 i, fun i => ρm i + c * w.2.2 i))
        = svfunRp gen H X s (c * w.1 + ρr') ((fun i => c * w.2.1 i) + ρr)
            ((fun i => c * w.2.2 i) + ρm) c := by
    intro ρr' ρr ρm
    have eAnn1 : (fun i => ρm i • s.1 + ρr i • gen)
        = (fun i => ((fun i => c * w.2.2 i) + ρm) i • s.1
            + ((fun i => c * w.2.1 i) + ρr) i • gen - c • s.2.1 i) := by
      funext i; rw [hC i]; simp only [Pi.add_apply, add_smul, mul_smul, smul_add]; abel
    have eAnn2 : (∑ i, ρr i • X i) - ρr' • H
        = (∑ i, ((fun i => c * w.2.1 i) + ρr) i • X i) - (c * w.1 + ρr') • H - c • s.2.2 := by
      rw [hZ]
      simp only [Pi.add_apply, add_smul, mul_smul, smul_sub, Finset.smul_sum,
        Finset.sum_add_distrib]
      abel
    have eR2 : (fun i => ρr i + c * w.2.1 i) = (fun i => c * w.2.1 i) + ρr := by
      funext i; simp only [Pi.add_apply]; ring
    have eR3 : (fun i => ρm i + c * w.2.2 i) = (fun i => c * w.2.2 i) + ρm := by
      funext i; simp only [Pi.add_apply]; ring
    simp only [svfunRp, eAnn1, eAnn2, eR2, eR3, add_comm ρr' (c * w.1)]
  simp only [hbody]
  refine (probOutput_bind_add_left_uniform (α := F) (m := c * w.1)
    (f := fun ρr' => ($ᵗ (Fin n → F) : ProbComp (Fin n → F)) >>= fun ρr =>
      ($ᵗ (Fin n → F) : ProbComp (Fin n → F)) >>= fun ρm =>
        pure (svfunRp gen H X s ρr' ((fun i => c * w.2.1 i) + ρr)
          ((fun i => c * w.2.2 i) + ρm) c)) (z := t)).trans ?_
  refine probOutput_bind_uniform_congr fun ρr' => ?_
  refine (probOutput_bind_add_left_uniform (α := Fin n → F) (m := fun i => c * w.2.1 i)
    (f := fun ρr => ($ᵗ (Fin n → F) : ProbComp (Fin n → F)) >>= fun ρm =>
      pure (svfunRp gen H X s ρr' ρr ((fun i => c * w.2.2 i) + ρm) c)) (z := t)).trans ?_
  refine probOutput_bind_uniform_congr fun ρr => ?_
  exact probOutput_bind_add_left_uniform (α := Fin n → F) (m := fun i => c * w.2.2 i)
    (f := fun ρm => pure (svfunRp gen H X s ρr' ρr ρm c)) (z := t)

end KVAC.Schemes.MicroCMZ
