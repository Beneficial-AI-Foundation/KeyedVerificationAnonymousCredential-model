/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.Group
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.ProgramLogic.Tactics

/-!
# μCMZ credential proof relations — Σ-protocols (O24 §5.1, Figure 9)

The keyed-verification credential μCMZ of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §5.1, proves three relations
`R_cmz = R_iu ∪ R_is ∪ R_p` (issuance-user, issuance-server, presentation).
They are built as VCVio `SigmaProtocol` instances, reusing the Schnorr template
(`.lake/packages/VCVio/Examples/Schnorr.lean`) generalized to vectors of
bases/scalars. **This file implements `R_iu`; `R_is` and `R_p` land in a
follow-up PR.**

All three are generalized-Schnorr Σ-protocols:

- **R_iu** (Eq. 9): the user proves knowledge of `(m⃗, s)` with
  `C' = Σᵢ mᵢ • Xᵢ + s • G`.
- **R_is** (Eq. 10): the issuer proves knowledge of `(x₀, u)` with
  `U' = u • G ∧ X₀ = x₀ • H ∧ V' = x₀ • U' + u • C''`.
- **R_p** (Eq. 11): the user proves knowledge of `(r', r⃗, m⃗)` with
  `(∀ i, Cᵢ = mᵢ • U' + rᵢ • G) ∧ Z = Σᵢ rᵢ • Xᵢ − r' • H`.
  (The `U' ≠ 0` check of Figure 9 is performed by the presentation verifier
  outside the proof, so it is not part of the relation.)

## Design: crs bases are parameters, keygen bases are in the statement

Following O24 Eq. 9, the per-issuer bases `X⃗` are part of the *statement*
(`R_iu`'s statement is the pair `(C', X⃗) : G × (Fin n → G)`), matching the
paper's instance `(C', X⃗, φ)`. Only the crs-derived generator `G` (and later
`H`) stays a *parameter* — legitimate because the paper indexes each relation
by the range of the crs, and `X⃗` is a keygen output (`Xᵢ = xᵢ • G`, part of
`pp`), not crs. This keeps `R_iu` structurally consistent with `R_is`/`R_p`,
whose public elements *must* live in the statement (e.g. `R_is` proves
`X₀ = x₀ • H`), so that `R_cmz = R_iu ∪ R_is ∪ R_p` can be formed cleanly.

`R_iu` is still total — for any `(C', X⃗)` a witness exists (take `m⃗ = 0` and
`s = (· • gen)⁻¹ C'`), since `· • gen` is a bijection — so it admits an honest
`GenerableRelation` whose `gen_uniform_right` reduces to the Pedersen-style
bijection argument. `R_is` and `R_p` are *not* total over their statement types,
so they carry no `GenerableRelation`; none is needed — only `R_iu` plays the
Fiat–Shamir keygen role.

TODO: The relations here use the trivial predicate `φ ≡ ⊤`; a non-trivial `φ` would
restrict the witness space and is deferred (it needs a witness-side subtype).

Each protocol comes with `PerfectlyComplete` and `SpeciallySound` proofs, a
transcript simulator, and an `HVZK` proof; the `R_iu` instances below are
complete, with `R_is`/`R_p` to follow in their PR.

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

/-- Pins `Inhabited F` so that instance search for the witness type's
`SampleableType ((Fin n → F) × F)` doesn't diverge through the `Module` /
`Subsingleton` instance graph when discharging its `Inhabited` side-goals
(see pitfall 2 above). File-local and high-priority so it never leaks. -/
private local instance (priority := high) : Inhabited F := ⟨0⟩

/-- Pins `Inhabited G` directly from `Zero G` (a projection of `AddCommGroup G`,
found without exploring the `OrderDual` graph). Needed so that the product
`SampleableType (G × (Fin n → G))` for the statement type discharges its
`Inhabited G` side-goal without diverging (see pitfall 2 above). Keyed on
`[Zero G]` — which mentions only `G` — so the synthesization order is
well-defined. File-local and high-priority so it never leaks. -/
private local instance (priority := high) [Zero G] : Inhabited G := ⟨0⟩

/-! ## Σ-protocol probability helpers

Small probability lemmas shared by the proofs below, written to avoid the
diverging `simp`/`rfl` on `Pr[…]` goals (see pitfall 1 above).

- **Completeness** (`probOutput_decide_bind₃/₄`): a computation that samples a
  few uniforms and returns a `decide` outputs `true` with probability 1 exactly
  when the decided predicate is universally true. Reduces a `PerfectlyComplete`
  goal to the underlying Boolean via `probOutput_eq_one_iff` (no failure +
  support is exactly `{true}`).
- **HVZK** (`probOutput_bind_uniform_congr`): two continuations that agree
  pointwise on output probability remain equal after a uniform bind — used to
  swap the real continuation for the simulated one in the HVZK proof. -/
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

/-- The R_iu relation (O24 Fig 9/Eq. 9, issuance user proof, with `φ ≡ ⊤`):
the statement is the pair `(C', X⃗) : G × (Fin n → G)` of the commitment and the
public bases; together with the crs generator `gen` it is satisfied by the
witness `(m⃗, s)` iff `C' = Σᵢ mᵢ • Xᵢ + s • gen`. -/
def riuRel (gen : G) : (G × (Fin n → G)) → ((Fin n → F) × F) → Bool :=
  fun stmt w => decide (stmt.1 = (∑ i, w.1 i • stmt.2 i) + w.2 • gen)

/-- R_iu as a Σ-protocol (a generalized Schnorr proof of knowledge of a
representation of `C'` in the bases `X⃗, G`). The statement is `(C', X⃗)`; the
public commitment is the announcement `R`; the challenge is a full-field scalar;
the response is the masked witness `(z⃗ₘ, zₛ)`. -/
def riuSigma (gen : G) :
    SigmaProtocol (G × (Fin n → G)) ((Fin n → F) × F) G ((Fin n → F) × F) F
      ((Fin n → F) × F) (riuRel gen) where
  commit s _w := do
    let ρ ← $ᵗ (Fin n → F)
    let ρs ← $ᵗ F
    return ((∑ i, ρ i • s.2 i) + ρs • gen, (ρ, ρs))
  respond _s w sc c := pure (fun i => sc.1 i + c * w.1 i, sc.2 + c * w.2)
  verify s R c z := decide ((∑ i, z.1 i • s.2 i) + z.2 • gen = R + c • s.1)
  sim s := do
    let ρ ← $ᵗ (Fin n → F); let ρs ← $ᵗ F
    return (∑ i, ρ i • s.2 i) + ρs • gen
  extract c₁ z₁ c₂ z₂ :=
    pure (fun i => (z₁.1 i - z₂.1 i) * (c₁ - c₂)⁻¹, (z₁.2 - z₂.2) * (c₁ - c₂)⁻¹)

/-- Completeness of the R_iu Σ-protocol: an honest prover with a valid witness
always convinces the verifier. Pure `Module` algebra (`add_smul`, `mul_smul`). -/
theorem riuSigma_complete (gen : G) :
    PerfectlyComplete (riuSigma (F := F) (n := n) gen) := by
  rintro ⟨Cp, X⟩ w h
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
theorem riuSigma_speciallySound (gen : G) :
    SpeciallySound (riuSigma (F := F) (n := n) gen) := by
  rintro ⟨Cp, X⟩ R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
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

/-- The simulated transcript tuple as a pure function of response `(a,b)` and
challenge `c`: announcement back-solved as `Σ aᵢ·Xᵢ + b·gen − c·C'`, paired with
`c` and `(a,b)`. `riuSimTranscript` is this with `(c,a,b)` sampled uniformly; the
HVZK proof rewrites the *real* transcript into this same form to compare. -/
private def simTranscriptValue (gen : G) (X : Fin n → G) (Cp : G)
    (a : Fin n → F) (b c : F) : G × F × (Fin n → F) × F :=
  ((∑ i, a i • X i) + b • gen - c • Cp, c, a, b)

/-- Transcript simulator for the R_iu Σ-protocol: sample the challenge and the
response uniformly and solve the verification equation for the announcement,
`R := (∑ᵢ zᵢ • Xᵢ) + zₛ • gen − c • C'`. -/
noncomputable def riuSimTranscript (gen : G) (stmt : G × (Fin n → G)) :
    ProbComp (G × F × ((Fin n → F) × F)) := do
  let c ← $ᵗ F
  let zm ← $ᵗ (Fin n → F)
  let zs ← $ᵗ F
  return (simTranscriptValue gen stmt.2 stmt.1 zm zs c)

/-- Honest-verifier zero-knowledge of the R_iu Σ-protocol (O24 Eq. 9): real
transcripts are distributed exactly as `riuSimTranscript`. -/
theorem riuSigma_hvzk (gen : G) :
    HVZK (riuSigma (F := F) (n := n) gen) (riuSimTranscript gen) := by
  rintro ⟨Cp, X⟩ w hrel
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
        = simTranscriptValue gen X Cp ((fun j => c * w.1 j) + ρ) (c * w.2 + ρs) c := by
    intro ρ ρs
    have e1 : (∑ i, ρ i • X i) + ρs • gen
        = (∑ i, ((fun j => c * w.1 j) + ρ) i • X i) + (c * w.2 + ρs) • gen - c • Cp := by
      rw [h_eq]
      simp only [Pi.add_apply, add_smul, mul_smul, smul_add, Finset.smul_sum,
        Finset.sum_add_distrib]
      abel
    have e3 : (fun i => ρ i + c * w.1 i) = (fun j => c * w.1 j) + ρ := by
      funext i; simp only [Pi.add_apply]; ring
    simp only [simTranscriptValue, e1, e3, add_comm ρs (c * w.2)]
  simp only [hbody]
  refine (probOutput_bind_add_left_uniform (α := Fin n → F) (m := fun j => c * w.1 j)
    (f := fun ρ => ($ᵗ F : ProbComp F) >>= fun ρs => 
      pure (simTranscriptValue gen X Cp ρ (c * w.2 + ρs) c))
    (z := t)).trans ?_
  refine probOutput_bind_uniform_congr fun ρ => ?_
  exact probOutput_bind_add_left_uniform (α := F) (m := c * w.2)
    (f := fun ρs => pure (simTranscriptValue gen X Cp ρ ρs c)) (z := t)

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

/-- The honest statement–witness generator for `R_iu`: sample the bases `X⃗`
and the witness `(m⃗, s)` uniformly and set the statement `(C', X⃗)` with
`C' = Σᵢ mᵢ • Xᵢ + s • gen`. Lifted out of the `GenerableRelation` structure so
the lemmas below are about a plain constant. -/
private noncomputable def riuGenComp (gen : G) :
    ProbComp ((G × (Fin n → G)) × ((Fin n → F) × F)) := do
  let X ← $ᵗ (Fin n → G)
  let m ← $ᵗ (Fin n → F)
  let s ← $ᵗ F
  return (((∑ i, m i • X i) + s • gen, X), (m, s))

private lemma riuGenComp_sound (gen : G) (y : G × (Fin n → G))
    (w : (Fin n → F) × F) (h : (y, w) ∈ support (riuGenComp (F := F) gen)) :
    riuRel gen y w = true := by
  simp only [riuGenComp, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ,
    exists_true_left] at h
  obtain ⟨X, m, s, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  simp only [riuRel, decide_eq_true_eq]

private lemma riuGenComp_uniform_left (gen : G) (w : (Fin n → F) × F) :
    Pr[= w | Prod.snd <$> riuGenComp (F := F) gen] =
      Pr[= w | ($ᵗ ((Fin n → F) × F) : ProbComp _)] := by
  rw [uniformSample_prod_eq]
  -- `snd <$> gen` drops the announcement; the leading base sample `X⃗` is unused,
  -- so it discards to the plain `(m⃗, s)` product.
  have hcomp : (Prod.snd <$> riuGenComp (F := F) gen)
      = (do let _X ← $ᵗ (Fin n → G)
            let m ← $ᵗ (Fin n → F); let s ← $ᵗ F; pure (m, s)) := by
    simp only [riuGenComp, map_bind, map_pure]
  rw [hcomp, probOutput_bind_of_const _ (fun _ _ => rfl), probFailure_uniformSample,
    tsub_zero, one_mul]

/-- For each fixed base vector `X⃗`, the commitment `C' = Σᵢ mᵢ • Xᵢ + s • gen`
is uniform over `G` (the `s • gen` term is a uniform shift, `· • gen` being a
bijection). This is the per-fibre uniformity used by `gen_uniform_right`. -/
private lemma riuGenComp_uniform_right_fibre (gen : G) (X : Fin n → G)
    (hgen : Function.Bijective (· • gen : F → G)) (c : G) :
    Pr[= c | (do let m ← $ᵗ (Fin n → F); let s ← $ᵗ F; pure ((∑ i, m i • X i) + s • gen))]
      = Pr[= c | ($ᵗ G : ProbComp G)] := by
  have hconst : ∀ m : Fin n → F,
      m ∈ support ($ᵗ (Fin n → F) : ProbComp (Fin n → F)) →
      Pr[= c | (do let s ← $ᵗ F; pure ((∑ i, m i • X i) + s • gen) : ProbComp G)]
        = Pr[= c | ($ᵗ G : ProbComp G)] := by
    intro m _
    have key := probOutput_bind_bijective_uniform_cross (α := F)
      (fun s : F => s • gen) hgen (fun y : G => pure ((∑ i, m i • X i) + y)) c
    have hadd := probOutput_add_left_uniform (α := G) (∑ i, m i • X i) c
    rw [map_eq_bind_pure_comp] at hadd
    simp only [Function.comp_def] at hadd
    exact key.trans hadd
  rw [probOutput_bind_of_const _ hconst, probFailure_uniformSample, tsub_zero,
    one_mul]

private lemma riuGenComp_uniform_right (gen : G)
    (hgen : Function.Bijective (· • gen : F → G)) (x : G × (Fin n → G)) :
    Pr[= x | Prod.fst <$> riuGenComp (F := F) gen] =
      Pr[= x | ($ᵗ (G × (Fin n → G)) : ProbComp _)] := by
  obtain ⟨c, xv⟩ := x
  -- `fst <$> gen` samples the bases `X⃗`, then announces `(C', X⃗)` with `C'`
  -- uniform in the fibre over `X⃗` (`riuGenComp_uniform_right_fibre`); the joint
  -- distribution is therefore uniform over `G × (Fin n → G)`.
  have hcomp : (Prod.fst <$> riuGenComp (F := F) gen)
      = (do let X ← $ᵗ (Fin n → G); let m ← $ᵗ (Fin n → F); let s ← $ᵗ F;
            pure ((∑ i, m i • X i) + s • gen, X)) := by
    simp only [riuGenComp, map_bind, map_pure]
  rw [hcomp, probOutput_bind_eq_tsum]
  -- Per fibre `X`, the second output coordinate pins `X = xv`; the first is uniform
  -- over `G` by `riuGenComp_uniform_right_fibre`.
  have hterm : ∀ X : Fin n → G,
      Pr[= (c, xv) |
          (do let m ← $ᵗ (Fin n → F)
              let s ← $ᵗ F
              pure ((∑ i, m i • X i) + s • gen, X) : ProbComp (G × (Fin n → G)))]
        = if xv = X then Pr[= c | ($ᵗ G : ProbComp G)] else 0 := by
    intro X
    have hmap :
        (do let m ← $ᵗ (Fin n → F)
            let s ← $ᵗ F
            pure ((∑ i, m i • X i) + s • gen, X) : ProbComp (G × (Fin n → G)))
        = (·, X) <$>
            (do let m ← $ᵗ (Fin n → F)
                let s ← $ᵗ F
                pure ((∑ i, m i • X i) + s • gen) : ProbComp G) := by
      simp only [map_bind, map_pure]
    rw [hmap, probOutput_prod_mk_fst_map]
    dsimp only
    rw [riuGenComp_uniform_right_fibre gen X hgen c]
  -- The RHS product sample factors into the two component probabilities.
  have hrhs : Pr[= (c, xv) | ($ᵗ (G × (Fin n → G)) : ProbComp (G × (Fin n → G)))]
      = Pr[= c | ($ᵗ G : ProbComp G)]
        * Pr[= xv | ($ᵗ (Fin n → G) : ProbComp (Fin n → G))] := by
    change Pr[= (c, xv) | ((·, ·) <$> ($ᵗ G) <*> ($ᵗ (Fin n → G)) :
        ProbComp (G × (Fin n → G)))] = _
    exact probOutput_seq_map_prod_mk_eq_mul ($ᵗ G) ($ᵗ (Fin n → G)) c xv
  simp only [hterm]
  rw [tsum_eq_single xv (fun X hX => by rw [if_neg (Ne.symm hX), mul_zero]),
      if_pos rfl, hrhs, mul_comm]

/-- R_iu is a generable relation: sample the bases `X⃗` and witness `(m⃗, s)`
uniformly and set the statement `(C', X⃗)` with `C' = Σᵢ mᵢ • Xᵢ + s • gen`.
Requires `· • gen` to be a bijection `F → G` (true when `gen` generates a
prime-order group with `|F| = |G|`); carried as a hypothesis here, exactly as
VCVio's Pedersen development does.

The fields are standalone private lemmas (about the lifted-out generator
`riuGenComp`) assembled by plain term application — running tactics inside
this dependent structure's fields does not terminate. -/
noncomputable def riuGen (gen : G)
    (hgen : Function.Bijective (· • gen : F → G)) :
    GenerableRelation (G × (Fin n → G)) ((Fin n → F) × F) (riuRel gen) where
  gen := riuGenComp gen
  gen_sound := riuGenComp_sound gen
  gen_uniform_left := riuGenComp_uniform_left gen
  gen_uniform_right := riuGenComp_uniform_right gen hgen

end KVAC.Schemes.MicroCMZ
