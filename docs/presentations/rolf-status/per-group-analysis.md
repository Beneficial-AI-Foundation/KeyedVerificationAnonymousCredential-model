# The per-group model and O24's Section 5

Analysis supporting the status presentation (2026-07-30). Paper: Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
("O24"), as `docs/Orru_2024.pdf`. Formalization: `KVAC/` with VCV-io.

## Statements are GrGen-based; proofs are per-group

O24 states every theorem of Section 5 over Γ ← GrGen(1<sup>λ</sup>), with
advantages as functions of λ. The proofs argue at a fixed group throughout:

- Lemma 5.4 (p. 37): the reduction "takes as input some group description Γ
  and (X, X′, X″) ∈ 𝔾³"; the simulation and the AGM polynomial case analysis
  run inside that Γ, over ℤ_p[η, x₀, xᵣ, x₁, u₁, …]. (Lemma 5.4 states 1/p
  for a degree ≤ 3 identity where a Schwartz–Zippel count gives 3/p;
  Theorem 5.1 assembles 3/p. The Lean reduction will compute the exact
  constant.)
- Lemma 5.5: the adversary takes "the public parameters (Γ, H, X₀, …, Xₙ)".
- Claim 5.6: the gap-DL reduction "takes as input (Γ, X)".

Nothing uses the distribution GrGen places on groups, so for each adversary
the proofs establish the inequality at every admissible fixed Γ, and
averaging over Γ yields the GrGen statements. Three qualifications: the
averaging is per adversary, not over per-group optimized advantages; it
applies to O24's reduction, which receives Γ as input — lifting the Lean
theorem itself would additionally need the reduction packaged as one program
over encoded descriptions (see the GrGen section); and c/p averages to an
expectation over p(Γ) unless GrGen fixes the order at each λ.

## Why the formalization is per-group

1. The inequality holds with no resource bound: it relates advantages of
   concrete adversaries and reductions (the AGM restriction remains).
   Formalizing the asymptotic wrapper would put a cost-model obligation on
   every reduction (VCV-io's `Asymptotics`/`CostModel` layers) without adding
   algebraic content.
2. It is the form a deployment instantiates. Signal's zkgroup runs on
   ristretto255, prime order ℓ = 2<sup>252</sup> +
   27742317777372353535851937790883648493, so 3/p ≈ 2<sup>−250</sup> — the
   statistical term only. The deployment posits concrete bounds for the
   assumption terms (3-DL, DL), informed by the best-known attacks; the
   inequality is the probability accounting, not a standalone security
   estimate, and for Theorem 5.1 it is additionally conditional on the AGM
   and the pending well-behaved bridge.
3. The content is preserved: the GrGen theorem follows by averaging, under
   the qualifications above; the converse does not hold in general (GrGen can
   hide a rare bad group).

## Consequences for the remaining theorems of Section 5

**AGM-shaped (5.3, 5.11–5.14).** Same anatomy as 5.1: reductions receive Γ,
AGM case analysis, bad events costing c/p; per-group is the native form. The
assumption side is merged (`twoDlogAdv`, `gapDlogAdv` in
`Assumptions.lean`). Query counts stay explicit parameters, as in
Theorem 5.3's Adv<sup>omuf</sup> ≤ Adv<sup>2-dl</sup> + q·Adv<sup>dl</sup> +
(q+5)/p. (The underlying Theorem 5.11 proves the finer (q+6)/p +
(q+1)·Adv<sup>dl</sup> + 3·Adv<sup>2-dl</sup> + Adv<sup>gapdl</sup>, which
does not visibly reduce to the headline; the formalization must reconcile
them.)

**Hypothesis-style (5.2, 5.10).** Conditional on a proof system for
R ⊇ R<sub>cmz</sub>; the proofs are game hops, each bounded at fixed Γ. Two
consequences:

1. For the interactive instantiation µCMZ[ZKP = Σ] the zero-knowledge terms
   vanish: perfect HVZK is exact distribution equality, so O24's statistical
   anonymity remark becomes an exact statement. The compiled NIZK's
   zero-knowledge term is a separate random-oracle object and does not
   vanish by this argument.
2. The knowledge-soundness terms are pending, and the extraction notion
   matters: O24 uses straight-line simulation extractability in the AGM and
   ROM (§9; Remark 5.9 gives when plain knowledge soundness suffices).
   Forking-lemma extraction (VCV-io's `Fork.lean`,
   `probOutput_none_fork_le`) does not by itself supply straight-line
   extraction inside an adaptive issuance simulator; this layer must
   formalize §9's argument or prove a weaker notion sufficient. It is the
   Fiat–Shamir gap of the status slides.

**Cross-cutting.** "n = poly(λ)" becomes "any fixed n" (an explicit
parameter, a different reading rather than a stronger one). Statistical and
perfect claims become exact bounds; computational hops keep their assumption
terms. Final numbers come from instantiating at the deployment group.

## What modeling with GrGen would change, and what it would gain

**Change.** (1) The group becomes data instead of ambience: Lean cannot
sample a type inside `ProbComp`, so GrGen needs a λ-indexed universe of
group descriptions plus interpretation, and every carrier becomes dependent
on the sampled description — the largest refactor, touching essentially all
of `KVAC/`. (2) Advantages become functions of λ; mechanical once (1)
exists. (3) Adversaries become λ-indexed families with resource bounds, and
every reduction acquires a PPT obligation (`Asymptotics`/`Negligible` plus a
cost model).

**Gain.** (1) Statement-level fidelity: theorems reading like
Adv<sub>GrGen</sub>(λ), and "µCMZ is secure" as one closed proposition.
(2) The one substantive gain: a machine-checked uniformity and efficiency
certificate for the reductions, today checkable only by inspection.

**No gain.** No better bound, no added deployment relevance, and
negligibility is strictly less informative than the concrete inequality.

**Middle ground.** Gain 2 does not require GrGen: VCV-io's query tracking
adds per-group bounds "B makes at most q<sub>A</sub> + c oracle queries";
local computation needs the cost-model layer on top. With both, per-group
covers everything GrGen would except the textual match and the packaged
uniformity statement.

## Modeling boundaries (Q&A material)

Boundaries of the formalization track, not divergences from O24 (the paper
does not treat them inside its theorems either).

1. **No executable randomness.** Sampling is ideal and exact (`ProbComp`,
   `evalDist`); an implementation's PRG sits below the model.
2. **No group encoding.** The group is an abstract typeclass. ristretto255
   supplies the prime-order abstraction and canonical encodings; decoding
   failures, canonicality checks, transcript framing, and side channels
   remain implementation obligations.
3. **No cost model.** Adversaries are arbitrary probabilistic programs;
   reductions are not proven efficient (future work, per the middle ground
   above).
4. **No serialization or domain separation.** These belong to the pending
   Fiat–Shamir layer, with the ROM, statement binding, and extraction
   losses; straight-line extraction (§9) is sequenced with Theorem 5.2.
5. **No nontrivial policy.** Only `trivialPolicy` discharges `Enforces`. A
   proper φ needs a combined proof binding φ to the same extracted witness,
   an efficiently provable representation, and the policy's identity bound
   into the transcript (else policy substitution).
6. **U′ ≠ 0 lives outside R<sub>p</sub>**, next to the proof check, faithful
   to Figure 9; the composition is an obligation of the pending presentation
   flow.
7. **Generator validity.** The security layer assumes (· • `gen`) bijective
   (`glog` well defined), which prime order supplies for any nonzero
   element.
8. **Credential-level theorems are not yet consequences.** Theorems 5.2 and
   5.10 need the flows (PR #77), the NIZK layer (PR #54), and the bridges on
   the design-decisions slide, beyond the proven MAC and Σ-protocol lemmas.

## Repo mapping

| Paper object | Formalization |
| --- | --- |
| Γ ← GrGen(1<sup>λ</sup>) | typeclass `SampleableGroup F G` plus the generator parameter `gen`; no sampling |
| Adv<sup>3-dl</sup><sub>GrGen</sub>(λ) | `threeDlogAdv g A` (`qdlogAdv 3`), fixed g, no λ |
| Adv<sup>dl</sup><sub>GrGen</sub>(λ) | `dlogAdv g A` over VCV-io's `DiffieHellman.dlogExp` |
| Adv<sup>gapdl</sup><sub>GrGen</sub>(λ) | `gapDlogAdv g A` |
| UF-CMVA(+Help) game, AGM | `AGM_UF_CMVAGame`, `AGM_UF_CMVAAdv` (`KVAC/Schemes/MicroCMZ/AlgebraicMAC.lean`) |
| Theorem 5.1's bound | `agm_ufcmva_le_n1`, `agm_ufcmva_le` (module `AGMReduction`, PR #88) |
