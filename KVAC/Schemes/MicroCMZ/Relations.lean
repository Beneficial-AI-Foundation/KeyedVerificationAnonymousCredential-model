/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.Group
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.ProgramLogic.Tactics

/-!
# μCMZ credential proof relations — Σ-protocols (O24 §5.1, Figure 9)

The keyed-verification credential μCMZ of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552, §5.1, proves three relations
`R_cmz = R_iu ∪ R_is ∪ R_p` (issuance-user, issuance-server, presentation).
**This file implements `R_iu`; `R_is` and `R_p` land in follow-up PRs.**

All three are generalized-Schnorr Σ-protocols:

- **R_iu** (Eq. 9): the user proves knowledge of `(m⃗, s)` with
  `C' = Σᵢ mᵢ • Xᵢ + s • G`.
- **R_is** (Eq. 10): the issuer proves knowledge of `(x₀, u)` with
  `U' = u • G ∧ X₀ = x₀ • H ∧ V' = x₀ • U' + u • C''`.
- **R_p** (Eq. 11): the user proves knowledge of `(r', r⃗, m⃗)` with
  `(∀ i, Cᵢ = mᵢ • U' + rᵢ • G) ∧ Z = Σᵢ rᵢ • Xᵢ − r' • H`.
  (The `U' ≠ 0` check of Figure 9 is performed by the presentation verifier
  outside the proof, so it is not part of the relation.)

## Statement layout

Per O24 Eq. 9, the `R_iu` statement is the triple `(C', X⃗, φ)` (commitment,
public bases, issuance predicate); only the crs generator `G` (later `H`) is a
parameter, since `X⃗` is a keygen output (`Xᵢ = xᵢ • G`) and `φ` is deployment
configuration. The base credential instantiates `φ` with `trivialPolicy`.

Soundness for a non-trivial `φ` is conditional on `Enforces`: the linear `verify`
checks only the representation equation, so it cannot enforce `φ` on extracted
witnesses; `trivialPolicy` discharges `Enforces` (`enforces_trivialPolicy`).
`PerfectlyComplete` and `HVZK` hold for any `φ` (neither touches `φ`).

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

/-- Pins `Inhabited F` to keep `SampleableType ((Fin n → F) × F)` synthesis
from diverging through the `Module`/`Subsingleton` graph (pitfall 2).
File-local, high-priority. -/
private local instance (priority := high) : Inhabited F := ⟨0⟩

/-- Pins `Inhabited G` from `Zero G` (avoiding the divergent `OrderDual` graph)
for product `SampleableType` synthesis (pitfall 2). Keyed on `[Zero G]` for a
well-defined search order. File-local, high-priority. -/
private local instance (priority := high) [Zero G] : Inhabited G := ⟨0⟩

/-! ## Σ-protocol probability helpers

Small probability lemmas for the proofs below, written to avoid divergent
`simp`/`rfl` on `Pr[…]` (pitfall 1): `probOutput_decide_bind₃/₄` (completeness)
and `probOutput_bind_uniform_congr` (HVZK). -/
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

/-- Congruence under a uniform bind: pointwise-equal output probabilities give
equal bound computations. -/
private lemma probOutput_bind_uniform_congr {A γ : Type} [SampleableType A]
    {k₁ k₂ : A → ProbComp γ} {t : γ} (h : ∀ a, Pr[=t | k₁ a] = Pr[=t | k₂ a]) :
    Pr[=t | (($ᵗ A : ProbComp A) >>= k₁)] = Pr[=t | (($ᵗ A : ProbComp A) >>= k₂)] := by
  rw [probOutput_bind_eq_tsum ($ᵗ A) k₁ t, probOutput_bind_eq_tsum ($ᵗ A) k₂ t]
  exact tsum_congr fun a => by rw [h a]

/-! ## R_iu — issuance user proof (O24 Eq. 9) -/

/-- Public bases `X⃗` (O24 Eq. 9): `Fin n → G`. -/
abbrev RiuBases (G : Type) (n : ℕ) : Type := Fin n → G

/-- Issuance predicate `φ` (O24 Eq. 9): `(Fin n → F) → Bool`. -/
abbrev RiuPolicy (F : Type) (n : ℕ) : Type := (Fin n → F) → Bool

/-- R_iu statement `(C', X⃗, φ)` (O24 Fig 9 / Eq. 9):
`G × RiuBases G n × RiuPolicy F n`. Right-associated: `stmt.1 = C'`,
`stmt.2.1 = X⃗`, `stmt.2.2 = φ`. -/
abbrev RiuStmt (G : Type) (F : Type) (n : ℕ) : Type :=
  G × RiuBases G n × RiuPolicy F n

/-- No-policy predicate `φ ≡ ⊤` (O24 anonymous-token / base-credential case). -/
def trivialPolicy : RiuPolicy F n := fun _ => true

/-- R_iu relation (O24 Fig 9 / Eq. 9): `(C', X⃗, φ)` holds for witness `(m⃗, s)`
iff `C' = Σᵢ mᵢ • Xᵢ + s • gen ∧ φ m⃗`. Use `trivialPolicy` for the no-policy
case. -/
def riuRel (gen : G) : RiuStmt G F n → ((Fin n → F) × F) → Bool :=
  fun stmt w => decide (stmt.1 = (∑ i, w.1 i • stmt.2.1 i) + w.2 • gen) && stmt.2.2 w.1

/-- R_iu as a generalized-Schnorr Σ-protocol (O24 Fig 9): PoK of a
representation of `C'` in bases `X⃗, G`. `verify` checks only the linear
equation; `φ`-enforcement on extracted witnesses is the `Enforces` hypothesis
(see `riuSigma_speciallySoundAt`). -/
def riuSigma (gen : G) :
    SigmaProtocol (RiuStmt G F n) ((Fin n → F) × F) G
      ((Fin n → F) × F) F ((Fin n → F) × F) (riuRel gen) where
  commit s _w := do
    let ρ ← $ᵗ (Fin n → F)
    let ρs ← $ᵗ F
    return ((∑ i, ρ i • s.2.1 i) + ρs • gen, (ρ, ρs))
  respond _s w sc c := pure (fun i => sc.1 i + c * w.1 i, sc.2 + c * w.2)
  verify s R c z := decide ((∑ i, z.1 i • s.2.1 i) + z.2 • gen = R + c • s.1)
  sim s := do
    let ρ ← $ᵗ (Fin n → F); let ρs ← $ᵗ F
    return (∑ i, ρ i • s.2.1 i) + ρs • gen
  extract c₁ z₁ c₂ z₂ :=
    pure (fun i => (z₁.1 i - z₂.1 i) * (c₁ - c₂)⁻¹, (z₁.2 - z₂.2) * (c₁ - c₂)⁻¹)

/-- Completeness (O24 Fig 9): an honest prover always convinces the verifier.
Holds for any `φ` — `verify` ignores the `φ` arm. -/
theorem riuSigma_complete (gen : G) :
    PerfectlyComplete (riuSigma (F := F) (n := n) gen) := by
  rintro ⟨Cp, X, φ⟩ w h
  simp only [riuRel] at h
  obtain ⟨hlin, _hφ⟩ := Bool.and_eq_true_iff.mp h
  have h_eq : Cp = (∑ i, w.1 i • X i) + w.2 • gen := of_decide_eq_true hlin
  simp only [riuSigma, bind_assoc, pure_bind]
  have hverify : ∀ (ρ : Fin n → F) (ρs c : F),
      (∑ i, (ρ i + c * w.1 i) • X i) + (ρs + c * w.2) • gen
        = ((∑ i, ρ i • X i) + ρs • gen) + c • Cp := by
    intro ρ ρs c
    rw [h_eq]
    simp only [add_smul, mul_smul, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
    abel
  exact probOutput_decide_bind₃ _ fun ρ ρs c => decide_eq_true (hverify ρ ρs c)

/-- `verify` enforces `φ`: every witness the extractor can produce from two
accepting transcripts (same announcement, distinct challenges) satisfies `φ`.
For `R_iu` instantiated with `fun w => stmt.2.2 w.1`. Provable for
`φ = trivialPolicy` (`enforces_trivialPolicy`); a `verify` that checks `φ` in
ZK would discharge it for a proper `φ`.

Stated generically over `σ` so the definition needs no group instances. -/
def Enforces {S W PC SC Ω P : Type} {p : S → W → Bool}
    (σ : SigmaProtocol S W PC SC Ω P p) (stmt : S) (φ : W → Bool) : Prop :=
  ∀ (R : PC) (c₁ c₂ : Ω) (z₁ z₂ : P), c₁ ≠ c₂ →
    σ.verify stmt R c₁ z₁ = true →
    σ.verify stmt R c₂ z₂ = true →
    ∀ w ∈ support (σ.extract c₁ z₁ c₂ z₂), φ w = true

/-- `trivialPolicy` is enforced by any `verify` (it holds of every `m⃗`). -/
theorem enforces_trivialPolicy (gen : G) (Cp : G) (X : RiuBases G n) :
    Enforces (riuSigma (F := F) (n := n) gen) (Cp, X, trivialPolicy)
      (fun w => trivialPolicy w.1) := by
  rintro _ _ _ _ _ _ _ _ w _
  rfl

/-- Special soundness (O24 Fig 9), conditional on `Enforces`: two accepting
transcripts (same announcement, distinct challenges) extract to a witness
satisfying the linear equation and `φ`. Discharge `hφ` with
`enforces_trivialPolicy` for `φ = trivialPolicy`. -/
theorem riuSigma_speciallySoundAt (gen : G) (Cp : G) (X : RiuBases G n)
    (φ : RiuPolicy F n)
    (hφ : Enforces (riuSigma (F := F) (n := n) gen) (Cp, X, φ) (fun w => φ w.1)) :
    SpeciallySoundAt (riuSigma (F := F) (n := n) gen) (Cp, X, φ) := by
  intro R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  have hφw : φ w.1 = true := hφ R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [riuSigma] at h_v1 h_v2 h_w
  simp only [support_pure, Set.mem_singleton_iff] at h_w
  subst h_w
  simp only [decide_eq_true_eq] at h_v1 h_v2
  simp only [riuRel, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hφw⟩
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

/-- Special soundness at `trivialPolicy` for every statement (discharges
`Enforces` via `enforces_trivialPolicy`). -/
theorem riuSigma_speciallySoundAt_trivial (gen : G) (Cp : G) (X : RiuBases G n) :
    SpeciallySoundAt (riuSigma (F := F) (n := n) gen) (Cp, X, trivialPolicy) :=
  riuSigma_speciallySoundAt gen Cp X trivialPolicy (enforces_trivialPolicy gen Cp X)

/-- Simulated transcript as a function of response `(a,b)` and challenge `c`:
announcement `R = Σ aᵢ·Xᵢ + b·gen − c·C'`, paired with `(c, (a,b))`.
`riuSimTranscript` samples `(c,a,b)` uniformly. -/
private def simTranscriptValue (gen : G) (X : RiuBases G n) (Cp : G)
    (a : Fin n → F) (b c : F) : G × F × (Fin n → F) × F :=
  ((∑ i, a i • X i) + b • gen - c • Cp, c, a, b)

/-- HVZK simulator (O24 Fig 9): sample `(c, z⃗ₘ, zₛ)` uniformly and back-solve
`R = Σ zᵢ•Xᵢ + zₛ•gen − c•C'`. -/
noncomputable def riuSimTranscript (gen : G) (stmt : RiuStmt G F n) :
    ProbComp (G × F × ((Fin n → F) × F)) := do
  let c ← $ᵗ F
  let zm ← $ᵗ (Fin n → F)
  let zs ← $ᵗ F
  return (simTranscriptValue gen stmt.2.1 stmt.1 zm zs c)

/-- HVZK (O24 Eq. 9): real transcripts match `riuSimTranscript` exactly. -/
theorem riuSigma_hvzk (gen : G) :
    HVZK (riuSigma (F := F) (n := n) gen) (riuSimTranscript gen) := by
  rintro ⟨Cp, X, φ⟩ w hrel
  simp only [riuRel] at hrel
  obtain ⟨hlin, _hφ⟩ := Bool.and_eq_true_iff.mp hrel
  have h_eq : Cp = (∑ i, w.1 i • X i) + w.2 • gen := of_decide_eq_true hlin
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

end KVAC.Schemes.MicroCMZ
