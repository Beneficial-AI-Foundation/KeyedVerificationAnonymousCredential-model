# Findings and lessons from Oana

This is based on:

- the crs sampling fix (#149, PR #216, merged 12 October);
- the Lemma 5.5 proofs document (`docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`, PR #212, merged 9 October) and the errata candidates it produced (#217);
- the reading for #240.

Rows marked *proposed, unreviewed* are in #217 since 3 October and not in `errata.md` on main; for those rows the "Errata section" column quotes the item's heading in #217, since the item has no section in `errata.md` yet.

## Part A. Findings about the paper

### A1. Bounds and probabilities stated wrongly (right arguments, wrong relation or probability)

| Errata # | Errata section | What is wrong | Origin |
|---|---|---|---|
| 19 (proposed, unreviewed) | "Lemmas 5.4 and 5.5 are stated with '='" (pp. 36, 38) | Both lemmas write Adv^ufcmva = Adv^3-dl + …. The advantage is per adversary, and the adversary whose forgery has U* = 0_𝔾 has advantage 0 while the right-hand side is at least 1/p. A reduction gives "≤", as Theorem 5.1 (p. 35) states. | Lemma 5.5 proofs document (PR #212); #217 |
| 21 (proposed, unreviewed) | "Claims 5.6 and 5.7 state their failure probabilities backwards" (p. 39) | Claim 5.6: "non-trivial with overwhelming probability 1/p"; the event holds with probability 1 − 1/p. Claim 5.7: "X₁ ≠ 0_𝔾 (which happens with probability 1/p)"; Pr[X₁ ≠ 0_𝔾] = 1 − 1/p. The bounds are unaffected. | Lemma 5.5 proofs document (PR #212); #217 |

### A2. Typos in the equations

| Errata # | Errata section | What is wrong | Origin |
|---|---|---|---|
| 17 (proposed, unreviewed) | "Claim 5.7 omits x_r" (pp. 39–40) | The claim runs A on (X₀, X₁, …, X_n) without X_r, and its verification equation has no x_r term, although the reduction's own input is (Γ, H, X₀, X_r, X₁). | Lemma 5.5 proofs document (PR #212); #217 |
| 20 (proposed, unreviewed) | "Claim 5.6: dropped and mixed indices" (p. 39) | The extraction formula writes m* for m*ᵢ in both sums; the Sign reply writes the queried message as m_{j,i} in one sum and mᵢ in the other. Neither slip affects the argument. | Lemma 5.5 proofs document (PR #212); #217 |

### A3. The scheme in the figure is not the scheme in the proof

| Errata # | Errata section | What is wrong | Origin |
|---|---|---|---|
| 13 | "Figure 9 samples H ←$ 𝔾, but §2.1.1 presents G and H as generators" (pp. 11, 34) | H = 0_𝔾 with probability 1/p. At H = 0_𝔾 the presentation's C_V collapses to V′ = s·U′, a distinguisher holding sk wins with advantage above 1 − 4/p against every simulator, and Theorem 5.8 is false as stated. | #149 (corrected Example 1); PR #216, merged 12 October |
| 14 | "Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0_𝔾" (pp. 40–41) | The real U′ = rU is uniform on 𝔾^×, the simulated U′ is 0_𝔾 with probability 1/p: statistical distance 1/p where H5 claims perfect indistinguishability. | #149 (action 2); PR #216, merged 12 October |
| 15 | "Sim.P's Z omits the x_r U′ term" (pp. 34, 40–41) | Sim.P computes Z = x₀U′ + Σᵢ γᵢXᵢ − C_V, the server computes Z = (x₀ + x_r)U′ + Σᵢ xᵢCᵢ − C_V; they differ by x_r U′. The simulator needs X_r in its state to add the term. | #149 (action 3); PR #216, merged 12 October |
| 22 (proposed, unreviewed) | "Figure 9 samples U ←$ 𝔾, against Definition 3.1's correctness" (pp. 25, 34) | µCMZ.M draws U ←$ 𝔾 while µCMZ.V rejects U = 0_𝔾, so an honest MAC fails to verify with probability 1/p, against Definition 3.1's "every honestly generated MAC verifies". Eq. (1) (p. 11) draws U ←$ 𝔾^× for CMZ. | Lemma 5.5 proofs document (PR #212); #217 |

What we did about items 13 and 22. The formalization samples H in `setup` and U in `mac` from 𝔾^× (`uniformNonzero`); proofs recover H ≠ 0 from `mem_support_setup`. Recorded in `docs/DESIGN_ALTERNATIVES.md`: *Nonzero crs H ←$ 𝔾^× where Figure 9 prints 𝔾* (merged, PR #216) and, proposed on #217, *Nonzero tag base U ←$ 𝔾^× in the base MAC*.

### A4. Things the paper leaves implicit that the formalization had to decide

This is not an error. It is a place where the paper says less than a machine needs; the decision is open.

- The running-time bound on the Sim of Definition 4.4 and the Ext of Definition 4.5 (#240, open). O24 fixes none; the two reference papers read for #240 fix the ZK simulator as PPT and the knowledge-soundness extractor as expected polynomial time. The bound that the formalization's Definitions 4.4 and 4.5 (`Anonymous`, `Extractable`) adopt is the formalization's choice, decided by what the Lean proofs of Theorems 5.8 and 5.10 establish for the simulator and extractor they build.

### A5. Proof steps missing as printed

| Errata # | Errata section | What is wrong | Origin |
|---|---|---|---|
| 16 (proposed, unreviewed) | "Claim 5.6's simulated Verify omits the U ≠ 0_𝔾 check" (p. 39) | Figure 9's verifier accepts iff U ≠ 0_𝔾 and the equation holds; the simulated Verify tests only the equation. On Verify(m, (0_𝔾, 0_𝔾)) the simulation answers 1 and the real oracle 0, so the simulation is not perfect as printed. | Lemma 5.5 proofs document (PR #212); #217 |
| 18 (proposed, unreviewed) | "Claim 5.7 forwards messages but not algebraic representations" (pp. 39–40) | The n → 1 reduction plays the 1-attribute AGM game, so the queries it relays and its forgery need representations over the 1-attribute basis. The paper collapses messages and never mentions representations; the missing step folds α₂, …, α_n into the X₁ coordinate at Verify, Help and the forgery. | Lemma 5.5 proofs document (PR #212); #217 |


## Part B. Lessons from doing the work

1. **Write the paper's proof out in full before formalizing it.** Writing out the proofs of Lemma 5.5 and Claims 5.6–5.7 yielded seven errata candidates (#217): a missing check in a simulated oracle, a missing step in the n → 1 reduction, a sampler contradicting the correctness definition, four slips in symbols and probabilities. A Lean statement fixes what a theorem says; only the written proof checks its every step.
2. **Ask "what if it is zero" of every sampled or received value, in the paper and in the code.** Put to Figure 9 and the simulator, it gave errata 13, 14 and 22; item 13 (H = 0) falsifies Theorem 5.8 as stated. Put to the implementations by a colleague, it gave three code findings: a `finalize` accepting P = 0, an unvalidated base, a Pedersen base taken from the issuer. None is visible from the Lean model.
3. **A fidelity claim quotes the paper; a reading is recorded as a reading.** The entry proposed on #240 said "the paper requires both to be p.p.t."; O24 bounds neither the simulator nor the extractor, in Definitions 4.4 and 4.5 or in §3.3, and the literature splits on the zero-knowledge adversary. Where the paper is silent, the choice is decided by what the formalization's proofs establish.
4. **Post only what you have verified yourself; an assistant's draft is a lead, not a finding.** Drafts for PRs #213 and #216 contained an invented lemma name, a stale file count and a wrong diff count; what went out was the subset checked at the source. The rules since: agents in ask mode, every command explained before approval, every quoted line re-read in the file, verified and inferred kept apart.
