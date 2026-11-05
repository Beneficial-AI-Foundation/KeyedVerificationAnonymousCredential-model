# Findings and lessons from Christiano

31 October 2026. This report rests on

- the proof-system layer, §3.3 (#26, #45 to #47, #54, #101);
- the framework games of §4 and the anonymity theorem (#185, #186, #10, #227, #228, #177);
- the extractability setting of Theorem 5.10 (#179, #242, #243);
- the credential correctness and the Theorem 5.3 statement (#206, #184, branch `microcmz-theorem-5-3`);
- the crs sampling plan on #149 (comment of 24 September, actions 2 and 3, implemented by #216);
- the reviews of #57, #88, #204, #214 and #216, with the issues they opened (#235, #236, #240);
- the preparation of `docs/findings/FINDINGS_AND_LESSONS.md`.

Errata numbers refer to `docs/presentations/rolf-status/errata.md`, items 18 and 19 on the branch of #184. DA refers to an entry of `docs/DESIGN_ALTERNATIVES.md`. The mark *shared* flags an item that another team mate found in part, and the row names this report's part.

## Part A. Findings about the paper

### A1. Bounds

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 12 (*shared*) | "Claim 5.13's bound has no term for Verify queries (pp. 46–47)" | A forger with no Sign query and Q < p Verify queries learns x₀ + xᵣ with probability (Q+1)(p−1)/p², then wins whenever H ≠ 0. The reduction of Claim 5.13 extracts nothing from it. Jin's PR #204 carried the Verify example in its module docstring. This report's part is the probability, the observation that the extraction recovers nothing, and the naming of the gap as an erratum, in the review of #204 of 29 September. | Review of #204 |

### A2. Typos in the equations

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 16 | "Hybrid H2 of Theorem 5.8 charges ZKP_cmz.iu for the simulation of π_p (p. 41)" | The displayed bound of hybrid H2 charges the zero knowledge of ZKP_cmz.iu where the simulated proof is π_p of ZKP_cmz.p. The Lean statement `μCMZ_anonymity` charges ZKP_cmz.p. | Theorem 5.8 statement (#10, #228) |

### A3. The scheme in the figure is not the scheme in the proof

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 8 (*shared*) | "Figure 9 writes ℤ_p where §5.1 and correctness need ℤ_p^× (pp. 33–34)" | Jin's first form (#147) covered the issuance nonce u and the issuance rerandomizer r. This report's part extends it to the presentation rerandomizer, with the table of failures and the correctness accounting through `μCMZCredential_correctRO` (#206). | Credential correctness (#206) |
| 14 | "Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0_𝔾 (pp. 40–41)" | Sim.P draws U′ from the whole group, so the simulated U′ is 0 with probability 1/p, while the real U′ = rU is never 0. Hybrid H5 claims perfect indistinguishability where the statistical distance is 1/p. | Comment on #149 of 24 September, action 2. Oana wrote the erratum from it in #216 |
| 15 | "Sim.P's Z omits the x_rU′ term (pp. 34, 40–41)" | Sim.P computes Z without the term xᵣU′ that the server computes, so the simulated π_p fails verification. The repair draws t from the nonzero scalars, sets U′ := tG and adds tXᵣ to Z, so the simulator needs Xᵣ in its state. | Comment on #149 of 24 September, action 3. Oana wrote the erratum from it in #216 |

What the formalization does about items 14 and 15. The simulator `μCMZAnonSimulator` (#228) samples u′ from the nonzero scalars, sets U′ = u′G and adds u′Xᵣ to Z, which then equals the server's Z.

### A4. The overview statements disagree with the theorems the paper proves

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 17 | "Theorem 1 prints Adv^simex where Theorem 5.8 prints Adv^ksnd (pp. 4, 40, 42)" | Theorem 1 and Theorem 5.8 differ in the extraction term, and Remark 5.9 justifies knowledge soundness for Schnorr proofs alone, while the paper prints Theorem 5.8 for any proof system. | Theorem 5.8 statement (#10, #227, #228) |
| 18 | "Theorem 5.3 charges Adv^zk_cmz.iu to a scheme without π_iu (pp. 35, 40–41)" | Theorem 5.3 copies the anonymity bound of Theorem 5.8, whose first term pays for hybrid H1, while the token's user sends no π_iu, so the term is vacuous. | Theorem 5.3 statement (#184, branch) |
| 19 | "Theorem 5.3 prints the one-more unforgeability bound of the October 2024 version (pp. 35, 43)" | Theorem 5.3 prints Adv^2dl + q·Adv^dl + (q+5)/p, the summary bound of the ePrint version of 3 October 2024. The revision of 24 February 2025 rewrote the proof of Theorem 5.11 into Claims 5.12 to 5.14 with a new bound, and Theorem 5.3 was never updated. None of the three versions examined proves the printed bound. | Theorem 5.3 statement (#184, branch) |

What the formalization does. The anonymity theorem `μCMZ_anonymity` (#228) keeps the printed Adv^ksnd of Theorem 5.8 and takes the condition of Remark 5.9 as hypotheses, each proof system, simulator and extractor confined to a region of the random-oracle domain, the regions pairwise disjoint. The Remark is the lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated` (#227) over any proof system. Two limits stand. The Remark's requirement that simulated proofs "cannot be turned into proofs" of the other relation has no formal counterpart, and no call site discharges the hypotheses before the compiled Σ-protocols of #3 exist (DA *Theorem 5.8 with the printed knowledge-soundness term*). The Theorem 5.3 statement on the branch, `μCMZAT_anonymous_token`, takes its clauses from Theorems 5.8 and 5.11, anonymity with the Theorem 5.8 simulator minus its π_iu part, one-more unforgeability with the Theorem 5.11 bound plus the π_is term.

### A5. Things the paper leaves implicit that the formalization had to decide

These are not errors, apart from one reading of a printed φ as a typo. Each decision is in DA with the rejected alternative and the fidelity argument.

**The proof-system layer, §3.3.**

- **Monadic verifier.** `verify` returns `M Bool`, since the paper writes 0/1 ← ZKP.V with a sampling arrow and a Fiat–Shamir verifier recomputes its challenge through the random oracle (#45).
- **Proveᵦ guard on the oracle side.** The Proveᵦ oracle checks (x, w) ∈ R and answers `none` on a non-witnessed query, identically in both worlds. A type-level guard on the query would narrow the game's interface (#47).
- **Relation decidability scoped to the game.** A `Decidable` instance is data, so the zero-knowledge game takes it as an argument and `relation` stays a `Prop`.
- **White-box knowledge-soundness extractor.** The extractor takes the adversary value and the run's observables, as §3.3 has Ext take "the random coins and the code" of A. Rewinding is out of scope, the §9 instantiation being straight-line (#54).
- **Carrier `OracleComp (ZKRO H)` for setup, prove and verify.** One carrier, so `verify` reads the oracle the proof was built with. A lemma under #101 will show that `verify` draws no coins of its own.
- **Extractor and simulator exhibited existentially** (*shared*, Tom Shrimpton raised the point, #43). The security statements exhibit both, in place of fields of the scheme.

**The framework, §4.**

- **Correctness requires issuance to succeed before presentation runs.** The experiment asks for the event σ ≠ ⊥ ∧ b = 1, since the paper defines presentation on credentials only.
- **No obligation theorem for `ExtractablePoly`.** The theorem of #126 asserting extractability for every scheme without premises was false, and #177 removed it. The asymptotic clause of Theorem 5.10 needs a λ-indexed group family (#148).
- **Anonymity game at fixed setup, negligibility over instance families.** The games take the crs, the keys, the attributes, the predicate and the initial table as parameters, as Definition 4.4 quantifies pointwise, since a game that samples setup bounds an average and an average does not bound every crs (#185, #186).
- **The issuer adversary runs before and after the user's request**, with random-oracle access in both runs, so a simulator that reprograms the oracle at its first move is detectable (#186).
- **Two adversary structures, not one pair.** A and D are separate, since the statistical and everlasting variants of Definition 4.4 constrain them separately (#186).
- **The anonymity simulator runs in the random-oracle state monad**, so it may reprogram the table, the power §3.3 grants a simulator (#186).
- **The Present oracle answers under the queried predicate** φ′, the printed φ being read as a typo (#186).
- **The extractor of Definition 4.5 takes the random-oracle table** as of the call and runs in `ProbComp`, since the proof of Theorem 5.10 builds it from the proof systems' extractors, which read the trace (#179).

**The MAC and its reductions, §5.3.**

- **Conditioned η masks** (*shared*, the obligation is Oana's). After #216 draws H from the nonzero elements, the game equality of Lemma 5.4 is false unless the reduction conditions the η masks on H ≠ 0. The conditioning is #229.
- **Theorem 5.10 at the honest UF-CMVA game with Help.** The unforgeability term of Theorem 5.10 is the advantage in the honest Figure 5 game with Help answered by the challenger, since the proof of Theorem 5.10 uses Help's answer and the paper ties Help to no model (#243).

**Anonymity of μCMZ, §5.4.**

- **Theorem 5.8 at a fixed crs.** The §3.3 advantages in the bound are taken on views that fix the crs at the H of the anonymity game, since a pointwise advantage is not bounded by sampled ones in general (#228).
- **The anonymity simulator takes a trace extractor.** Definition 4.4 puts ∃Sim before ∀A, so the simulator cannot depend on the adversary a `KSNDExtractor` takes. The §9 extractor also reads the algebraic representations, which the instantiation of #3 must carry in the proof or in the table (#228).

**Open.** The crs and the group (#148). The instance fixes the group and the generator as type parameters, so every theorem is an inequality at one group, and the asymptotic predicates are not provable for μCMZ until a λ-indexed family exists.

## Part B. Findings about the formalization

1. **`WellBehaved` formalized the printed theorem, not the one the proof establishes.** The review of #214 (13 October) found that the hypothesis quantifies over every key, crs and parameters where Figure 5 samples them. It also forbids Help queries, which the paper adds one paragraph after Theorem 5.1 for the proof of Theorem 5.10 to use. Issue #236 asked for a proof that `WellBehaved` is the algebraic condition of Theorem 5.1, which the docstring claimed and nothing proved. Issue #235 proposed restricting the adversary type in place of the gate, "The paper has no gate." Semar's report records the restriction adopted on 23 October, the day #236 closed as not planned. PRs #246 and #247 merged 30 October.
2. **Adversary classes and the paper's p.p.t. class** (#240). Every adversary is an `OracleComp` computation with no running time. Under "for all adversaries" the wider class strengthens a theorem, under "there exists a simulator" it weakens a definition. Without coins the class of Lemmas 5.4 and 5.5 held only the deterministic forgers of the paper, which #232 fixed for the one-more forgers. O24 bounds neither the simulator of Definition 4.4 nor the extractor of Definition 4.5, so the bound the formalization adopts is its own choice.
3. **The design record misread Claim 5.7.** The entry said the paper's reduction owes no translation of algebraic representations. Lemma 5.4 holds in the algebraic group model (p. 36), so the reduction to n = 1 relays representations over the 1-attribute basis, as the written proof of Lemma 5.5 (#212) had said. Item A5.2 of `docs/findings/FINDINGS_AND_LESSONS.md` is the corrected record.
4. **Structured hash domains** (*shared*, the design choice is Jin's, #57). The review of 16 July characterized the abstract `Dom` as a stronger oracle model than bitstrings, with the injective encoding and the domain separation as obligations of a concrete instantiation, and asked for the entry.

## Part C. Lessons from doing the work

1. **Summary theorems drift from the theorems the paper proves.** Errata 18 and 19 are copies that no revision updated, erratum 17 a copy that changed a term. Derive the overview statement from the theorems the paper proves, with the version history of the paper in hand.
2. **The order of quantifiers decides what a simulator may see.** Placing ∃Sim before ∀A rules out a simulator that reads the adversary, which motivates a trace extractor. An oracle adversary that queries at any time forces two runs of the issuer.
3. **Pointwise and sampled quantifiers need a bridge.** Definition 4.4 quantifies over every crs while the §3.3 games sample it, and an average does not bound every point. The fixed group is the same question one level up (#148).
4. **A theorem without premises about every scheme is false.** The obligation theorem of #126 asserted extractability for every scheme. A statement that holds for a class of schemes names the class or goes.
5. **The paper is the source of truth. A problem in it gets a mathematical fix.** When the code base lacks the game a theorem needs, the team builds the game. The theorem keeps its statement instead of fitting the game at hand. The Theorem 5.3 clause on one-more unforgeability waits for the algebraic game of the scheme with π_is (#184).
6. **A statement-first review checks fidelity to the printed statement, so it cannot catch a theorem that formalizes the wrong statement faithfully.** The review of #214 read the statement alongside the paper's proof and the downstream track that consumes it, Theorem 5.10.
7. **Report a departure early, in the author's terms.** Erratum 7 went to Rolfe on 20 August with a proposed correction and the plan to build the core first. When the same question returned two months later, the entry answered it.

## Part D. Lessons about the use of AI assistants

1. **The use of AI across the team has to be consistent.** Terms with no basis in the paper or in the literature, "constant audit", "collapse" and "direction" for the scalars of the reduction to n = 1, entered docstrings and blueprint nodes through one assistant, and other assistants copied them from file to file. The rule that bans coined terms in new text extends to the terms already in the code base. The team replaces them and grandfathers none. The pull request of `docs/findings/FINDINGS_AND_LESSONS.md` carries the first replacements.
2. **The code base is not a source of truth for an assistant.** The paper and the written proofs are, and the code base reflects them. When a docstring or a design entry becomes the reference an assistant reads, an error propagates. The design record's reading of Claim 5.7 (Part B, 3) went from the design record into the module docstring and into the first draft of the team report, although the paper states Lemma 5.4 in the algebraic group model and the written proof of Lemma 5.5 had already said so.
