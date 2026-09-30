/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Credential
import KVAC.Framework.Correctness
import KVAC.Framework.Extractability
import KVAC.Core.NIZKP.Completeness

/-!
# Correctness of the μCMZ credential (O24 Definition 4.3)

The μCMZ credential `μCMZCredentialSyntax` of Figure 9 of Orrù, *Revisiting Keyed-Verification
Anonymous Credentials*, IACR ePrint 2024/1552 (O24), satisfies `CorrectRO`, the support-based
form of O24 Definition 4.3 at the oracle carrier `OracleComp (ZKRO HS)`. The theorem
`μCMZCredential_correctRO` states it.

## Hypotheses

The three proof systems are parameters of the instance, so correctness needs their completeness.
Each hypothesis is `PerfectlyComplete` (O24 §3.3) of the proof system's `toNIZKPSyntax`, with the
crs setup `H ←$ G` lifted into the oracle carrier and the relation `R_cmz.iu`, `R_cmz.is` or
`R_cmz.p` of `Relations.lean`. The generator must be nonzero, as for `μCMZATCore_correct`, since
the server's `U' = u·gen` must pass the user's check `U' ≠ 0`.

## Completeness at every cache

`PerfectlyComplete` asks the prover to start from a cache that the setup reaches from `∅`. Here
that cache is `∅` alone. Issuance runs the prover of `π_is` from the cache that `π_iu` left, and
presentation runs the prover of `π_p` from the cache that issuance left. The theorem
`ProofSystemFor.verify_of_perfectlyComplete` closes the difference. The theorem
`runRO_support_of_le` replays every run of the prover followed by the verifier from `∅`, so a
rejection from any cache yields a rejection from `∅`.

## Structure

The issuance half `credIssue_correct` and the presentation half `credPresent_correct` hold from
every cache. The issuance half yields a MAC code that passes the base-MAC check `verify`. The
presentation half accepts every MAC code that passes it, under a satisfied `φ'`. The theorem
`μCMZCredential_correctRO` removes the lifted `setup` and `keygen` with
`mem_support_runRO_liftM_iff` and composes the two halves.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

variable (HS : HashSpec)

/-- The support of `runRO` on a bind. The pair `(b, c'')` is an outcome of `x >>= f` from the cache
`c` iff some outcome `(a, c')` of `x` from `c` has `(b, c'')` as an outcome of `f a` from `c'`. -/
lemma mem_support_runRO_bind {α β : Type} (c : HS.spec.QueryCache)
    (x : OracleComp (ZKRO HS) α) (f : α → OracleComp (ZKRO HS) β) (b : β)
    (c'' : HS.spec.QueryCache) :
    (b, c'') ∈ support (runRO HS c (x >>= f)) ↔
      ∃ a c', (a, c') ∈ support (runRO HS c x) ∧ (b, c'') ∈ support (runRO HS c' (f a)) := by
  simp only [runRO, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, Prod.exists]

/-- The support of `runRO` on `pure a` from the cache `c` is the single pair `(a, c)`. -/
lemma mem_support_runRO_pure {α : Type} (c : HS.spec.QueryCache) (a b : α)
    (c' : HS.spec.QueryCache) :
    (b, c') ∈ support (runRO HS c (pure a : OracleComp (ZKRO HS) α)) ↔ b = a ∧ c' = c := by
  simp [runRO]

omit [DecidableEq G] in
/-- Perfect completeness at every random-oracle cache. Let `π` be `PerfectlyComplete` with the crs
setup `H ←$ G` and the relation `rel`. For a witnessed statement, a proof `p` produced from any
cache `c`, and a bit `b` of the verifier run from the cache the prover leaves, `b = true`.

The prover followed by the verifier from `c` replays from `∅ ≤ c` by `runRO_support_of_le`. The
lifted setup reaches every `H` with the cache `∅`, so `PerfectlyComplete` applies to the replay. -/
theorem ProofSystemFor.verify_of_perfectlyComplete [SampleableType G] {Stmt Witness : Type}
    (π : ProofSystemFor (OracleComp (ZKRO HS)) G Stmt Witness) (rel : G → Stmt → Witness → Bool)
    (hπ : PerfectlyComplete HS
      (π.toNIZKPSyntax (fun _ => liftM ($ᵗ G)) (fun crs x w => rel crs x w = true)))
    {crs : G} {x : Stmt} {w : Witness} (hrel : rel crs x w = true)
    {c : HS.spec.QueryCache} {p : π.Proof} {c₁ : HS.spec.QueryCache}
    (hp : (p, c₁) ∈ support (runRO HS c (π.prove crs x w)))
    {b : Bool} {c₂ : HS.spec.QueryCache}
    (hb : (b, c₂) ∈ support (runRO HS c₁ (π.verify crs x p))) : b = true := by
  -- The combined run of prover and verifier from `c` replays from the empty cache.
  have hrun : (b, c₂) ∈ support (runRO HS c (π.prove crs x w >>= π.verify crs x)) :=
    (mem_support_runRO_bind HS c _ _ b c₂).mpr ⟨p, c₁, hp, hb⟩
  obtain ⟨c₂', hrun'⟩ := runRO_support_of_le HS (bot_le : (⊥ : HS.spec.QueryCache) ≤ c) _ hrun
  obtain ⟨p', c₁', hp', hb'⟩ := (mem_support_runRO_bind HS ⊥ _ _ b c₂').mp hrun'
  -- The lifted setup reaches `crs` with the empty cache.
  have hsetup : (crs, (∅ : HS.spec.QueryCache)) ∈ support ((simulateQ (zkROImpl HS)
      (liftM ($ᵗ G) : OracleComp (ZKRO HS) G)).run ∅) :=
    (mem_support_runRO_liftM_iff HS ∅ ($ᵗ G) crs ∅).mpr ⟨by simp, rfl⟩
  exact hπ 0 crs ∅ hsetup x w hrel p' c₁' hp' b c₂' hb'

/-- The issuance half of the correctness of the μCMZ credential (O24 Definition 4.3, Figure 9).
Take keys in the support of `keygen H gen`, so that `pp = (x₀·H, xᵣ·gen, (xᵢ·gen)ᵢ)`, and
attributes `m⃗` with `φ(m⃗) = 1`. From every cache, every issuance outcome is a MAC code that passes
the base-MAC check `verify`.

The completeness of `π_iu` and of `π_is` discharges both verifications. The nonzero nonce `u` and
`gen ≠ 0` pass the check `U' ≠ 0`. The unblinding algebra
`V' − s·U' = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·U'` gives the MAC equation, as in `μCMZATCore_correct`. -/
theorem credIssue_correct (gen : G) (hgen : gen ≠ 0)
    (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
    (πp : ∀ n, RpProofSystem HS G F n)
    (hiu : ∀ n, PerfectlyComplete HS ((πiu n).toNIZKPSyntax (fun _ => liftM ($ᵗ G))
      (fun _ x w => riuRel gen x w = true)))
    (his : PerfectlyComplete HS (πis.toNIZKPSyntax (fun _ => liftM ($ᵗ G))
      (fun H x w => risRel (F := F) gen H x w = true)))
    {secParam n : ℕ} (H : G) (x₀ xᵣ : F) (x : Fin n → F) (m : Fin n → F) (φ : Policy F n)
    (hφ : φ m = true) {c c' : HS.spec.QueryCache} {σ? : Option (Code G)}
    (hσ : (σ?, c') ∈ support (runRO HS c
      ((μCMZCredentialSyntax F HS gen πiu πis πp).issue (secParam := secParam) H
        (x₀, xᵣ, x) (x₀ • H, xᵣ • gen, fun i => x i • gen) m φ))) :
    ∃ σ, σ? = some σ ∧ verify (x₀, xᵣ, x) m σ = true := by
  -- User, first move. Sample `s` and prove `π_iu`.
  simp only [KVACSyntax.issue, issueChain, μCMZCredentialSyntax, credIssueUsr₁,
    bind_assoc, pure_bind] at hσ
  obtain ⟨s, c₀, hs, h₁⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp hσ
  obtain ⟨-, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hs
  obtain ⟨π, c₁, hπ, h₂⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₁
  obtain ⟨o, c₂, ho, h₃⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₂
  -- Server. The proof `π_iu` verifies on the bases `credBases gen sk = X⃗`.
  unfold credIssueSrv at ho
  obtain ⟨b, c₃, hb, ho⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp ho
  have hrel : riuRel gen (∑ i, m i • x i • gen + s • gen, fun i => x i • gen, φ) (m, s) = true := by
    simp only [riuRel, hφ, Bool.and_true, decide_eq_true_eq]
  have hb' : (b, c₃) ∈ support (runRO HS c₁ ((πiu n).verify H
      (∑ i, m i • x i • gen + s • gen, fun i => x i • gen, φ) π)) := hb
  have hbt : b = true := ProofSystemFor.verify_of_perfectlyComplete HS (πiu n)
    (fun _ x w => riuRel gen x w) (hiu n) hrel hπ hb'
  subst hbt
  obtain ⟨u, c₄, hu₀, h₄⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp ho
  obtain ⟨hu, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hu₀
  rw [mem_support_uniformUnits] at hu
  obtain ⟨π', c₅, hπ', h₅⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₄
  obtain ⟨rfl, rfl⟩ := (mem_support_runRO_pure HS _ _ _ _).mp h₅
  -- User, second move. The check `U' ≠ 0` passes and `π_is` verifies.
  have hU' : u • gen ≠ 0 := smul_ne_zero hu hgen
  dsimp only at h₃
  unfold credIssueUsr₂ at h₃
  simp only [if_neg hU'] at h₃
  obtain ⟨b', c₆, hb'₀, h₆⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₃
  have hrel' : risRel gen H (x₀ • H, ∑ i, m i • x i • gen + s • gen + xᵣ • gen, u • gen,
      x₀ • u • gen + u • (∑ i, m i • x i • gen + s • gen + xᵣ • gen)) (x₀, u) = true :=
    decide_eq_true ⟨rfl, rfl, rfl⟩
  have hb't : b' = true := ProofSystemFor.verify_of_perfectlyComplete HS πis
    (fun H x w => risRel gen H x w) his hrel' hπ' hb'₀
  subst hb't
  simp only [if_true] at h₆
  obtain ⟨r, c₇, hr₀, h₇⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₆
  obtain ⟨hr, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hr₀
  rw [mem_support_uniformUnits] at hr
  obtain ⟨rfl, rfl⟩ := (mem_support_runRO_pure HS _ _ _ _).mp h₇
  -- The unblinded pair passes the base-MAC check.
  refine ⟨_, rfl, ?_⟩
  simp only [verify, macScalar, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨smul_ne_zero hr hU', ?_⟩
  -- `r·(V' − s·U') = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·(r·U')`, module algebra over `gen`.
  have hsum : (∑ i, m i • x i • gen) = (∑ i, x i * m i) • gen := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
  rw [hsum]
  simp only [smul_smul, ← add_smul, ← sub_smul]
  congr 1
  ring

/-- The presentation half of the correctness of the μCMZ credential (O24 Definition 4.3,
Figure 9). Take keys in the support of `keygen H gen`, a MAC code `σ` that passes the base-MAC
check `verify` for `m⃗`, and a policy with `φ'(m⃗) = 1`. From every cache, every presentation bit
is `true`.

The server's `Z = (x₀ + xᵣ)·U' + Σᵢ xᵢ·Cᵢ − C_V` equals the user's `Σᵢ rᵢ·Xᵢ − r'·H`, since
`V = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·U`. So both parties use the same `R_cmz.p` statement, and the
completeness of `π_p` discharges its verification. The rerandomized `U' = r·U` is nonzero since
`r ≠ 0` and `U ≠ 0`. -/
theorem credPresent_correct (gen : G)
    (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
    (πp : ∀ n, RpProofSystem HS G F n)
    (hp : ∀ n, PerfectlyComplete HS ((πp n).toNIZKPSyntax (fun _ => liftM ($ᵗ G))
      (fun H x w => rpRel (F := F) gen H x w = true)))
    {secParam n : ℕ} (H : G) (x₀ xᵣ : F) (x : Fin n → F) (m : Fin n → F) (σ : Code G)
    (hσ : verify (x₀, xᵣ, x) m σ = true) (φ' : Policy F n) (hφ' : φ' m = true)
    {c c' : HS.spec.QueryCache} {b : Bool}
    (hb : (b, c') ∈ support (runRO HS c
      ((μCMZCredentialSyntax F HS gen πiu πis πp).present (secParam := secParam) H
        (x₀, xᵣ, x) (x₀ • H, xᵣ • gen, fun i => x i • gen) m σ φ'))) :
    b = true := by
  obtain ⟨U, V⟩ := σ
  simp only [verify, macScalar, Bool.and_eq_true, decide_eq_true_eq] at hσ
  obtain ⟨hU, rfl⟩ := hσ
  simp only [KVACSyntax.present, μCMZCredentialSyntax, credPresentUsr, bind_assoc,
    pure_bind] at hb
  obtain ⟨coins, c₀, hcoins₀, h₁⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp hb
  obtain ⟨hcoins, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hcoins₀
  obtain ⟨r, r', rs⟩ := coins
  have hr : r ≠ 0 := by
    simp only [credPresentCoins, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, Prod.mk.injEq, exists_prop] at hcoins
    obtain ⟨r₀, hr₀, -, -, -, -, hrr, -, -⟩ := hcoins
    exact hrr ▸ (mem_support_uniformUnits F r₀).mp hr₀
  -- User. Prove `π_p`. Server. Recompute `Z` and verify `π_p`.
  obtain ⟨π, c₁, hπ, h₂⟩ := (mem_support_runRO_bind HS _ _ _ _ _).mp h₁
  -- The server tests `U' ≠ 0` before it verifies, and `r·U ≠ 0` since `r` is a unit.
  have hrU : r • U ≠ 0 := smul_ne_zero hr hU
  unfold credPresentSrv at h₂
  simp only [if_neg hrU] at h₂
  -- The server's `Z` equals the user's `Σᵢ rᵢ·Xᵢ − r'·H` on an honest MAC code.
  have hZ : (x₀ + xᵣ) • r • U + ∑ i, x i • (m i • r • U + rs i • gen) -
      (r • (x₀ + xᵣ + ∑ i, x i * m i) • U + r' • H) = ∑ i, rs i • x i • gen - r' • H := by
    have h₁ : ∑ i, x i • (m i • r • U + rs i • gen) =
        ((∑ i, x i * m i) * r) • U + (∑ i, rs i * x i) • gen := by
      simp only [smul_add, Finset.sum_add_distrib, smul_smul, Finset.sum_mul, Finset.sum_smul]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]
      · exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    have h₂ : ∑ i, rs i • x i • gen = (∑ i, rs i * x i) • gen := by
      simp only [smul_smul, Finset.sum_smul]
    rw [h₁, h₂]
    module
  have hrel : rpRel gen H (r • U, fun i => x i • gen, fun i => m i • r • U + rs i • gen,
      ∑ i, rs i • x i • gen - r' • H, φ') (r', rs, m) = true := by
    change (decide ((∀ i, _ = _) ∧ _ = _) && φ' m) = true
    rw [hφ', Bool.and_true]
    exact decide_eq_true ⟨fun _ => rfl, rfl⟩
  have hok' : (b, c') ∈ support (runRO HS c₁ ((πp n).verify H (r • U, fun i => x i • gen,
      fun i => m i • r • U + rs i • gen, ∑ i, rs i • x i • gen - r' • H, φ') π)) := by
    rw [← hZ]
    exact h₂
  exact ProofSystemFor.verify_of_perfectlyComplete HS (πp n)
    (fun H x w => rpRel gen H x w) (hp n) hrel hπ hok'

/-- Correctness of the μCMZ credential (O24 Definition 4.3, Figure 9) at the oracle carrier,
`CorrectRO` for `μCMZCredentialSyntax`. The hypotheses are a nonzero generator and the perfect
completeness of `π_iu`, `π_is` and `π_p` for `R_cmz.iu`, `R_cmz.is` and `R_cmz.p`.

The lifted `setup` and `keygen` leave the cache `∅`, and `mem_support_keygen` fixes `pp` from the
secret key. The theorem `credIssue_correct` yields a MAC code that passes `verify`, and
`credPresent_correct` accepts it. The theorem `newUsr_mac_isSome` consumes this statement. -/
theorem μCMZCredential_correctRO (gen : G) (hgen : gen ≠ 0)
    (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
    (πp : ∀ n, RpProofSystem HS G F n)
    (hiu : ∀ n, PerfectlyComplete HS ((πiu n).toNIZKPSyntax (fun _ => liftM ($ᵗ G))
      (fun _ x w => riuRel gen x w = true)))
    (his : PerfectlyComplete HS (πis.toNIZKPSyntax (fun _ => liftM ($ᵗ G))
      (fun H x w => risRel (F := F) gen H x w = true)))
    (hp : ∀ n, PerfectlyComplete HS ((πp n).toNIZKPSyntax (fun _ => liftM ($ᵗ G))
      (fun H x w => rpRel (F := F) gen H x w = true))) :
    CorrectRO HS (μCMZCredentialSyntax F HS gen πiu πis πp) := by
  intro secParam n _hn crs s₀ hsetup keys s₁ hkeys m φ φ' hφ hφ'
  -- The lifted `setup` and `keygen` leave the cache `∅`.
  obtain ⟨-, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hsetup
  obtain ⟨⟨x₀, xᵣ, x⟩, pp⟩ := keys
  obtain ⟨hk, rfl⟩ := (mem_support_runRO_liftM_iff HS _ _ _ _).mp hkeys
  have hpp := (mem_support_keygen (F := F) (G := G) crs gen x₀ xᵣ x pp).mp hk
  subst hpp
  -- Issuance yields a valid MAC code, and presentation accepts it.
  intro σ? s₂ hσ
  obtain ⟨σ, rfl, hv⟩ := credIssue_correct HS gen hgen πiu πis πp hiu his crs x₀ xᵣ x m φ hφ hσ
  exact ⟨σ, rfl, fun b ⟨_, hb⟩ =>
    credPresent_correct HS gen πiu πis πp hp crs x₀ xᵣ x m σ hv φ' hφ' hb⟩

end KVAC.Schemes.MicroCMZ
