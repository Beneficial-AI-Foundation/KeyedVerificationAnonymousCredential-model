# The per-group model and O24's Section 5

Analysis supporting the status presentation (2026-07-30). Paper: Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
("O24"), as `docs/Orru_2024.pdf`. Formalization: `KVAC/` with VCV-io.

## Statements are GrGen-based; proofs are per-group

O24 states every theorem of Section 5 in the GrGen model: each game samples a
group description Γ ← GrGen(1<sup>λ</sup>), and advantages are functions of λ.
Theorem 5.1 and the lemmas behind it (5.4, 5.5) all carry
Adv<sub>GrGen</sub>(λ) terms; none fixes a group.

The proofs argue at a fixed group throughout.

- Proof of Lemma 5.4 (p. 37): the reduction B "takes as input some group
  description Γ and (X, X′, X″) ∈ 𝔾³"; the simulated public parameters and
  signing answers are identically distributed within that Γ; the AGM case
  analysis runs over ℤ_p[η, x₀, xᵣ, x₁, u₁, …] with p the order of Γ's group;
  the bad-event bound is 3/p at that p.
- Proof of Lemma 5.5: "Let A be an adversary … taking as input the public
  parameters (Γ, H, X₀, …, Xₙ)".
- Claim 5.6: the gap-DL reduction B "takes as input (Γ, X)".

Nothing in these arguments uses the distribution GrGen places on groups. For
each adversary, the proofs establish the inequality at every admissible fixed
Γ; averaging that inequality over Γ ← GrGen(1<sup>λ</sup>) yields the GrGen
statements. The averaging is per adversary, with the reductions uniform in Γ
(they receive Γ as input); it is not an average of per-group optimized
advantages.

## Why the formalization is per-group

1. The per-group inequality needs no polynomial-time cost model. It relates
   the advantages of concrete adversaries and reductions, so it holds with no
   resource bound; the AGM restriction on the adversary remains. Formalizing
   the asymptotic wrapper would require a cost model on every reduction
   (VCV-io has `Asymptotics` and `CostModel` layers) without adding algebraic
   content.
2. The per-group form is the one a deployment instantiates. Signal's zkgroup
   runs on ristretto255, one fixed group of prime order
   ℓ = 2<sup>252</sup> + 27742317777372353535851937790883648493, so
   3/p ≈ 2<sup>−250</sup>. The security interpretation then plugs best-known
   attack costs into the assumption terms (3-DL, DL) at that group; the
   inequality itself carries no resource bound, so it is the probability
   accounting, not a standalone security estimate.
3. Nothing is lost. The GrGen theorem follows by averaging the per-group
   inequality; the converse does not hold in general (GrGen can hide a rare
   bad group).

## Consequences for the remaining theorems of Section 5

**AGM-shaped theorems (5.3, 5.11–5.14).** Same anatomy as Theorem 5.1:
GrGen statements, proofs whose reductions receive Γ and run an AGM polynomial
case analysis at that group with bad events costing c/p. The per-group
statement is the proofs' native form. The assumption side is in the repo
(`twoDlogAdv` for Theorem 5.3's 2-DL, `gapDlogAdv` for Claim 5.6, in
`KVAC/Preliminaries/Assumptions.lean`). Bounds with query counts, such as
Theorem 5.3's Adv<sup>omuf</sup> ≤ Adv<sup>2-dl</sup> + q·Adv<sup>dl</sup> +
(q+5)/p, keep q as an explicit parameter of the concrete inequality.

**Hypothesis-style theorems (5.2, 5.10).** Conditional statements: if ZKP is
a proof system for R ⊇ R<sub>cmz</sub>, then anonymity and extractability hold
with advantages bounded by sums of Adv<sup>zk</sup> and Adv<sup>ksnd</sup>
terms. The proofs are game hops, each bounded by a reduction at fixed Γ. Two
per-group consequences:

1. The ZKP advantage terms must be defined per-group, and for the formalized
   pieces they vanish: the interactive Σ-protocols have perfect HVZK and
   perfect special soundness, so the corresponding terms are 0 rather than
   negligible. O24's remark that µCMZ[ZKP = Σ] has statistical anonymity
   becomes an exact statement with a concrete bound.
2. The terms that do not vanish are the knowledge-soundness advantages of the
   Fiat–Shamir-compiled proofs. Per-group these become concrete forking-lemma
   bounds with explicit query counts (VCV-io formalizes the forking lemma in
   `CryptoFoundations/Fork.lean`, with the bound
   `probOutput_none_fork_le`). This coincides with the Fiat–Shamir gap on the
   Issuance status slide; the future work concentrates there.

**Cross-cutting.** "n = poly(λ)" becomes "any fixed n", a more general
reading. "Overwhelming in λ" claims become statistical-distance bounds at the
fixed group. Final numbers come from instantiating the inequality at the
deployment group, not from a limit argument.

## What modeling with GrGen would change, and what it would gain

Two axes hide in the question: sampling the group, and the asymptotic
machinery that usually rides along (polynomial-time adversaries,
negligibility).

**What would change.**

1. The group becomes data instead of ambience. Today `SampleableGroup F G` is
   a typeclass: every definition lives at an implicit fixed (G, gen), wired
   through by instance resolution. With GrGen the game's first line samples
   the group, and Lean cannot sample a *type* inside `ProbComp`, only a
   value. We would need a λ-indexed universe of group descriptions (a Σ-type
   bundling order, carrier representation, generator, and the group axioms)
   plus an interpretation function, and every carrier (`Key F n`,
   `Params G n`, tags, statements, witnesses) would depend on the sampled
   description. Typeclass-driven definitions become explicitly threaded
   record fields. This is the largest refactor; essentially every file in
   `KVAC/` touches it.
2. Advantages become functions of λ, with the outer probability over GrGen.
   Mechanical, once (1) exists.
3. Adversaries become λ-indexed families with resource bounds. Stating the
   paper's theorems as security (not just an identity of averages) requires
   "for every PPT adversary family, the advantage is negligible", which drags
   in VCV-io's `Asymptotics`/`Negligible` layer and a cost model, and every
   reduction B acquires a proof obligation that it is PPT given that A is.

**What we would gain.**

1. Statement-level fidelity: theorems that read like the paper's
   Adv<sub>GrGen</sub>(λ) forms, and "µCMZ is secure" as one closed
   proposition instead of an inequality schema.
2. A machine-checked uniformity and efficiency certificate for the
   reductions. This is the one substantive gain: the per-group inequality
   says nothing about the reductions' cost, and its security interpretation
   silently relies on B being cheap. Today that is checkable by inspection
   (B is an explicit `ProbComp` program) but not stated as a theorem.

**What we would not gain.** No better bound (the per-group inequality already
implies the averaged one, with identical constants), no additional deployment
relevance (a deployment fixes the group), and the negligibility conclusion is
strictly less informative than the concrete inequality it replaces.

**The middle ground.** Gain 2 does not require GrGen. VCV-io's query-tracking
and cost-model layers work per-group: theorems of the form "B makes at most
q<sub>A</sub> + c oracle queries" can be added to the existing fixed-group
reductions, capturing reduction efficiency concretely without touching the
group-sampling axis. Per-group plus query accounting dominates GrGen plus
negligibility on every axis except literal textual match with the paper.

## Repo mapping

| Paper object | Formalization |
| --- | --- |
| Γ ← GrGen(1<sup>λ</sup>) | typeclass `SampleableGroup F G` plus the parameter `gen` (G₀); no sampling |
| Adv<sup>3-dl</sup><sub>GrGen</sub>(λ) | `threeDlogAdv g A` (`qdlogAdv 3`), fixed g, no λ |
| Adv<sup>dl</sup><sub>GrGen</sub>(λ) | `dlogAdv g A` over VCV-io's `DiffieHellman.dlogExp` |
| Adv<sup>gapdl</sup><sub>GrGen</sub>(λ) | `gapDlogAdv g A` |
| UF-CMVA(+Help) game, AGM | `AGM_UF_CMVAGame`, `AGM_UF_CMVAAdv` (`KVAC/Schemes/MicroCMZ/AlgebraicMAC.lean`) |
| Theorem 5.1's bound | `agm_ufcmva_le_n1`, `agm_ufcmva_le` (forthcoming module `AGMReduction`) |
