# Findings and lessons from the repository record

This is based on:

- `docs/presentations/rolf-status/errata.md`, items 1 to 17 on `main`, items 18 and 19 on the branch `microcmz-theorem-5-3` (#184),
- `docs/DESIGN_ALTERNATIVES.md`, 36 entries on `main` and one on that branch,
- the seven errata candidates of #217 (Oana, 3 October), awaiting review, and the two of Semar's report of 28 October,
- the reports of Jin (21 October), Oana (23 October) and Semar (28 October) for the categories and the format.

Paper: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552, cited as O24, in its version of 27 March 2026 unless a version is named. Errata numbers refer to `errata.md`. The candidates of #217 carry their numbers there with the prefix P, since items 16 and 17 of `errata.md` took those numbers first. Semar's two candidates are S1 and S2. "DA" refers to an entry of `DESIGN_ALTERNATIVES.md`, by its heading. **Kind** says whether an item lives only in the security argument (*proof*) or constrains an implementation (*impl*), as input for KVAC-verify. **Status** says where the item stands, on `main`, proposed, or on a branch.

**Status on main.** The statements of Lemma 5.4, Lemma 5.5, Theorem 5.1 in its `WellBehaved` form, Theorem 5.8, and Theorem 5.11 with Claims 5.12 to 5.14 are on `main` with `sorry`, the blueprint reporting their proof status. The #235 stack restates Theorem 5.1 for the game with Help (PRs 246 and 247 approved, parts 3 to 7 to follow). Of the Theorem 5.10 stack, the game with Help (PR 243) and the framework extractor (PR 245) are merged, the setting (PR 244) is under review and the statement (PR 242) is a draft. The Theorem 5.3 statement is on its branch and postponed (#184). None of the findings below weakens a result. The assumptions are the paper's own. One unjustified summand is dropped (item 2), the additive constant of Theorem 5.1 goes from 3/p to 5/p, both about 2⁻²⁵⁰ at ristretto255, one zero-knowledge term enters the one-more unforgeability bound (item 7), and the overview bounds of Theorems 1 and 5.3 give way to the bounds of the theorems they summarize (items 17 to 19).

## Part A. Findings about the paper

### A1. Bounds and probabilities stated wrongly (the arguments are right, the constants or the relation are not)

| # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | The 1/p non-vanishing bound should be 3/p (p. 38) | The partial evaluation ψ of the forgery polynomial is nonzero "except with probability 1/p". Φ has total degree 3, so Schwartz–Zippel gives 3/p. | `agm_ufcmva_le_n1_explicit`, the term `3 * (card F)⁻¹` | proof | on `main` | Lemma 5.4 proof |
| 2 | Lemma 5.4's printed Adv<sup>dl</sup> summand has no reduction behind it (pp. 36–38) | The statement carries an Adv^dl term. The proof builds one reduction, to 3-DL, so the term is slack. | `agm_ufcmva_le_n1_explicit`, no DL term | proof | on `main` | Lemma 5.4 proof |
| 6 | Theorem 5.1's printed bound elides the gap-DL term | Lemma 5.5 sends the collision case to gap-DL, and the printed Theorem 5.1 bound drops that term. The formal bound is Adv^3-dl + Adv^gap-dl + 5/p. | `agm_ufcmva_le_explicit` | proof | on `main` | Lemma 5.5 statement (#209) |
| 12 | Claim 5.13's bound has no term for Verify queries (pp. 46–47) | A forger with no Sign query and Q Verify queries learns x₀ + xᵣ with probability (Q+1)/p and wins, and the reduction of Claim 5.13 extracts nothing from it. The bound needs a term in Q. | module docstring of `OneMoreUnforgeability/Statements.lean` | proof | on `main` | Theorem 5.11 statements (#189) |
| P19 | Lemmas 5.4 and 5.5 are stated with "=" (pp. 36, 38) | Lemmas 5.4 and 5.5 write Adv^ufcmva = Adv^3-dl + …. The adversary whose forgery has U* = 0 has advantage 0, so the relation is ≤, as Theorem 5.1 prints it. | `agm_ufcmva_le_n1_explicit`, `agm_ufcmva_le_explicit`, inequalities | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| P21 | Claims 5.6 and 5.7 state their failure probabilities backwards (p. 39) | Claims 5.6 and 5.7 attach 1/p to the event that holds with probability 1 − 1/p. The bounds are unaffected. | none | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |

**What we did.** Every formal statement is an inequality on named reductions. The bound of Theorem 5.1 is Adv^3-dl(B₁) + Adv^gap-dl(B_gap) + 5/p, where 5/p is 3/p (item 1), 1/p for Σᵢ Δᵢbᵢ = 0 in Claim 5.6 and 1/p for x₁ = 0 in Claim 5.7 (DA *Schwartz–Zippel bound 3/p, not the paper's 1/p*). The 3/p is the generic Schwartz–Zippel bound for a degree-3 polynomial, and the entry records that a structural argument might recover the printed 1/p, which the paper does not give. Item 12 is recorded in the module docstring of `OneMoreUnforgeability/Statements.lean` as an obligation on the Claims, whose constants are provisional until the Track CMZ-OMUF audit.

**Lesson.** A Lean statement must name every summand and the reduction behind it. A bound term without a reduction (item 2) has nowhere to come from, and a constant has to be derived (items 1, 6, 12). Four of the six were caught because a statement had to say which event has which probability.

### A2. Typos in the equations

| # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | Eq. 13: X₀'s X-coefficient (typo) | X₀'s X-coefficient drops the factor a₀. The correct coefficient is a₀b_h + b₀a_h. | `redTrace` | proof | on `main` | Lemma 5.4 coupling (#88) |
| 4 | Eq. 14: signing-response coefficient (typo) | Vⱼ's G-coefficient is a_{u,j}(a₀ + aᵣ + a₁mⱼ), not a_{u,j}(a_h a₀ + a_h + a₁mⱼ). | `reductionSignStep` | proof | on `main` | Lemma 5.4 coupling (#88) |
| 5 | Claim 5.6's extraction has the wrong sign (p. 39) | The extracted discrete logarithm has the wrong sign. | `gapDlReduction` | proof | on `main` | Lemma 5.5 (#208) |
| 9 | Claim 5.6 never defines X<sub>r</sub> (p. 39) | Xᵣ is used by the reduction and never defined. The key's constant part lacks xᵣ. | `gapDlKeyParts` | proof | on `main` | Lemma 5.5 (#207) |
| 10 | Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term (p. 39) | The Verify query subtracts zU alone where the full constant part cU must go. | `gapDlOracleImpl` | proof | on `main` | Lemma 5.5 (#207) |
| 11 | Claim 5.6's Verify query misplaces the inverse (p. 39) | The inverse applies to V alone instead of V − cU. | `gapDlOracleImpl` | proof | on `main` | Lemma 5.5 (#207) |
| 16 | Hybrid H2 of Theorem 5.8 charges ZKP<sub>cmz.iu</sub> for the simulation of π<sub>p</sub> (p. 41) | Hybrid H2's displayed bound charges ZKP_cmz.iu where the simulated proof is π_p of ZKP_cmz.p. | `μCMZ_anonymity` | proof | on `main` | Theorem 5.8 statement (#10) |
| P17 | Claim 5.7 omits x<sub>r</sub> (pp. 39–40) | Claim 5.7 runs A without Xᵣ and its verification equation has no xᵣ term, although the reduction's input has Xᵣ. | `nTo1Adversary` | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| P20 | Claim 5.6: dropped and mixed indices (typo, p. 39) | The extraction formula writes m* for m*ᵢ, and the Sign reply mixes mⱼ,ᵢ and mᵢ for one message. | none | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |

**What we did.** Each correction is documented at its use site in the reduction, `redTrace` and `reductionSignStep` for Eqs. 13 and 14 (DA *Eq. 13*, *Eq. 14*), `gapDlReduction`, `gapDlKeyParts` and `gapDlOracleImpl` for Claim 5.6. The Verify query of Claim 5.6 is formalized as Ddh(d·U, V − c·U), which needs no inverse and covers d = 0 as well (item 11). Item 16 is charged to ZKP_cmz.p in `μCMZ_anonymity`.

**Lesson.** None of these changes a result, and each stopped a proof until it was found. Eqs. 13 and 14 surfaced when the coupling between the reduction and the real game would not close with the printed coefficients. A reader who fills in the intended value never sees them.

### A3. The scheme in the figure is not the scheme in the proof

| # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 7 | Figure 9 boxes only π<sub>iu</sub>, but the Theorem 5.11 proof analyzes the scheme without π<sub>is</sub> (pp. 34–35, 40, 44) | Figure 9 removes π_iu only, Theorem 5.3 keeps π_is, and the proof of Theorem 5.11 analyzes the scheme with neither proof. | `μCMZATCoreSyntax`, `μCMZATSyntax`. `omufPiIsZKAdversary` on the branch | proof | on `main` | Theorem 5.3 track. Raised with Rolfe on 20 August |
| 8 | Figure 9 writes ℤ<sub>p</sub> where §5.1 and correctness need ℤ<sub>p</sub><sup>×</sup> (pp. 33–34) | Three scalars are drawn from ℤ_p where §5.1 needs ℤ_p^×. A zero draw makes an honest run fail. | `uniformUnits` in `credIssueSrv`, `credIssueUsr₂`, `credPresentUsr`, `atIssueSrv`, `atIssueUsr₂` | impl | on `main` | Theorem 5.3 track (#146, #147, #206) |
| 13 | Figure 9 samples H ←$ 𝔾, but §2.1.1 presents G and H as generators (pp. 11, 34) | H ←$ 𝔾 admits H = 0, where a distinguisher holding sk wins with advantage above 1 − 4/p and Theorem 5.8 is false. | `setup` with `uniformNonzero` | impl | on `main` | #149, PR #216 |
| 14 | Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0<sub>𝔾</sub> (pp. 40–41) | The simulated U′ is 0 with probability 1/p, the real one never. | `μCMZAnonSimulator`, u′ ←$ ℤ_p^× | proof | on `main` | #149, PR #216 |
| 15 | Sim.P's Z omits the x<sub>r</sub>U′ term (pp. 34, 40–41) | Sim.P's Z lacks the term xᵣU′ that the server computes. The simulator needs Xᵣ in its state. | `μCMZAnonSimulator`, the term `u' • pp.2.1` | proof | on `main` | #149, PR #216 and its review |
| P22 | Figure 9 samples U ←$ 𝔾, against Definition 3.1's correctness (pp. 25, 34) | μCMZ.M draws U ←$ 𝔾 while V rejects U = 0, so an honest MAC fails to verify with probability 1/p, against Definition 3.1. | `mac` with `uniformNonzero` | impl | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |

**What we did about item 7.** The scheme the proof of Theorem 5.11 analyzes, with neither issuance proof, is stated under its own name, `μCMZATCore`, and Theorem 5.11 is stated for it. The scheme of Figure 9 with π_is is `μCMZATSyntax` at the oracle carrier (#183). A lifting lemma, the simulation hybrid that replaces each real π_is by a simulated one at the cost of one Adv^zk_cmz.is term, returns to the paper's scheme (#205). The Theorem 5.3 statement carries that term through a named reduction with a `sorry` body (DA *The μCMZ_AT core removes both issuance proofs, not only the boxed π_iu*, and *Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11* on the branch). Jin raised the item with Rolfe on 20 August with this correction and the plan to build the core first, and Rolfe acknowledged it. The team did not wait for the paper's correction.

**What we did about items 8, 13, 14, 15 and P22.** The formalization draws the three scalars of Figure 9 and the tag base U from the nonzero elements with `uniformUnits` and `uniformNonzero`, and the crs H from 𝔾^× in `setup`, so an honest run never fails and `H ≠ 0` is recovered from `mem_support_uniformNonzero` where a proof needs it (DA *Nonzero issuance nonces*, *Nonzero crs H ←$ 𝔾^×*, and *Nonzero tag base U ←$ 𝔾^×* proposed on #217). The simulator `μCMZAnonSimulator` samples u′ ←$ ℤ_p^×, sets U′ = u′G and adds u′Xᵣ to Z, which equals the server's Z (items 14 and 15). Item 13 is the finding with the largest consequence. At H = 0 a distinguisher holding sk wins with advantage above 1 − 4/p against every simulator, so Definition 4.4 fails for μCMZ and no simulator repairs it.

**Lesson.** A figure, a theorem statement and a proof can describe three different schemes without anyone noticing, because a reader fills the gaps with the intended scheme. A formalization defines the game on one precise scheme, so it has to pick one and say so. Every sampler is a question, "what if it is zero", and the answer decides correctness (items 8, P22), a security theorem (item 13) or a simulation step (items 14, 15).

### A4. The overview statements disagree with the proved theorems

| # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 17 | Theorem 1 prints Adv<sup>simex</sup> where Theorem 5.8 prints Adv<sup>ksnd</sup> (pp. 4, 40, 42) | Theorem 1 prints Adv^simex where Theorem 5.8 prints Adv^ksnd, and Remark 5.9's bridge covers Schnorr proofs alone. | `μCMZ_anonymity`, `ksndSimAdv_le_ksndAdv_of_domainSeparated` | proof | on `main` | Theorem 5.8 statement (#10) |
| 18 | Theorem 5.3 charges Adv<sup>zk</sup><sub>cmz.iu</sub> to a scheme without π<sub>iu</sub> (pp. 35, 40–41) | Theorem 5.3's anonymity bound charges Adv^zk_cmz.iu for a proof the token's user never sends. | `μCMZAT_anonymous_token` | proof | on the branch `microcmz-theorem-5-3` (#184) | Theorem 5.3 statement (#184) |
| 19 | Theorem 5.3 prints the one-more unforgeability bound of the October 2024 version (pp. 35, 43) | Theorem 5.3 prints the one-more unforgeability bound of the ePrint version of October 2024, which no version proves. | `μCMZAT_anonymous_token`, `omufBound` | proof | on the branch `microcmz-theorem-5-3` (#184) | Theorem 5.3 statement (#184) |

**What we did.** The formalization states the proved theorems and derives the overview ones from them. `μCMZ_anonymity` keeps the printed Adv^ksnd of Theorem 5.8 and takes the condition of Remark 5.9 as hypotheses, since hybrid H3 extracts from a π_is produced after a simulated π_iu, which the knowledge-soundness game of §3.3 does not cover. The Remark is stated as the lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated` over any proof system, with an explicit region of the random-oracle domain for "the vector sizes mismatch" (DA *Theorem 5.8 with the printed knowledge-soundness term*). The Theorem 5.3 statement on the branch bounds anonymity by Adv^zk_cmz.p + Adv^ksnd_cmz.is, with the Theorem 5.8 simulator minus its π_iu part, and one-more unforgeability by the Theorem 5.11 bound `omufBound` plus the π_is term. The ePrint history settled item 19. The version of 3 October 2024 printed the Theorem 5.3 bound, the revision of 24 February 2025 rewrote the proof of Theorem 5.11 into Claims 5.12 to 5.14 and changed its bound, and Theorem 5.3 was never updated. Theorem 1 exists only from the version of 27 March 2026 and follows the revised Theorem 5.11.

**Lesson.** Theorems 1, 5.2 and 5.3 are copies of §5 results, and copies drift when the originals are revised. A summary theorem is stated as the conjunction of the theorems it summarizes, each read on the scheme the summary names, and the version history of the paper is part of the evidence.

### A5. Proof steps missing or misdirected as printed

| # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| P16 | Claim 5.6's simulated Verify omits the U ≠ 0<sub>𝔾</sub> check (p. 39) | The simulated Verify of Claim 5.6 tests the equation only and omits the check U ≠ 0, so it answers 1 on (0, 0) where the real oracle answers 0. | `gapDlOracleImpl` | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| P18 | Claim 5.7 forwards messages but not algebraic representations (pp. 39–40) | The n → 1 reduction forwards messages and never the algebraic representations the 1-attribute game needs. | `AGMRepr.collapseRepr`, `AGMRepr.linCombCollapse` | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| S1 | Eq. 14 gives the Verify arm two powers where the degree needs three (p. 37) | Eq. 14 gives Verify the powers (X, X′) only, "as the maximum degree of the resulting polynomial is 2". The verification polynomial has degree 3, so Verify needs X″ as Help does. | `exponentEval` | proof | proposed in Semar's report of 28 October, not yet on #217 | Lemma 5.4 coupling. Design record, *Eq. 14* |
| S2 | Lemmas 5.4 and 5.5 send Help to Theorem 5.11, whose proof never uses it (pp. 36, 38, 42–43) | The proofs of Lemmas 5.4 and 5.5 say that Help "will simplify the proof of Theorem 5.11". The proof that uses Help's answer is Theorem 5.10's, and the proof of Theorem 5.11 never mentions Help. | none | proof | proposed in Semar's report of 28 October, not yet on #217 | review of PR #243. Design record, *Theorem 5.10 at the honest UF-CMVA game with Help* |

**What we did.** The simulated Verify of the gap-DL reduction checks U ≠ 0 (`gapDlOracleImpl`, P16). The n → 1 reduction translates every coefficient list to the 1-attribute basis, `AGMRepr.collapseRepr` for one element and `AGMRepr.linCombCollapse` for the Help arm's weighted sum, an obligation the paper does not have (DA *Claim 5.7: the n → 1 collapse translates representations, not only messages*, P18). The Verify arm of the reduction evaluates against (G, X, X′, X″) as the Help arm does (`exponentEval`, S1). The Help cross-reference is recorded where Help is consumed, in the Theorem 5.10 setting (S2).

**Lesson.** Only the written proof checks every step. Oana's proofs document for Lemma 5.5 produced P16 to P22 on its own, from writing the printed proofs out in full, and the two of Semar came from a coupling that would not close and from a review of another track's PR.

### A6. Things the paper leaves implicit that the formalization had to decide

These are not errors. They are places where the paper says less than a machine needs, and the choice is recorded in `docs/DESIGN_ALTERNATIVES.md` with the decision, the rejected alternative and the fidelity argument. The entries that answer an erratum are cited above. The rest follow, by the layer of the paper they concern.

**The proof-system layer, §3.3.**

- **Security-model-agnostic specification set aside.** The NIZKP object is the game-based §3.3 specification. The earlier typeclass with model-supplied relations `indist`, `produces` and `extracts` stays in the tree and is not imported, since it abstracts away the computational content a §3.3 citation needs (#43).
- **Extractor and simulator exhibited existentially.** Both are exhibited in the security statements, not fields of the scheme, as in §3.3 and the standard definitions.
- **Monadic verifier.** `verify` returns `M Bool`, since the paper writes 0/1 ← ZKP.V with a sampling arrow and a Fiat–Shamir verifier recomputes its challenge through the random oracle.
- **Proveᵦ guard on the oracle side.** The Proveᵦ oracle checks (x, w) ∈ R and answers `none` on a non-witnessed query, identically in both worlds. A type-level guard on the query was rejected, since the check belongs to the oracle and a type restriction narrows the game's interface.
- **Relation decidability scoped to the game.** A `Decidable` instance is data, so it is supplied as an argument of the game that runs the guard, and `relation` stays a `Prop`.
- **White-box knowledge-soundness extractor.** The extractor takes the adversary value and the run's observables, the output, the final oracle table and, for simulation extractability, the simulation log, as §3.3 has Ext take "the random coins and the code" of A. Rewinding is out of scope, the §9 instantiation being straight-line. Whether an ordered query log is needed is open.
- **Carrier `OracleComp (ZKRO H)` for setup, prove and verify.** One carrier, so `verify` can read the oracle the proof was built against. That `verify` draws no coins of its own is deferred to a lemma (#101), two bespoke structures that fix it in the type being rejected for their cost at every use site.
- **Structured hash domains.** `HashSpec.Dom` is an arbitrary type, a stronger model than bitstrings, with the injective encoding and the domain separation as obligations of a concrete instantiation.

**The framework, §4.**

- **Exact-attribute predicate as a family field.** `PredicateFamily` carries φ_m⃗ with its semantic law, since Figure 8's NewUsr runs issuance under it. The rest of the partial-disclosure family is #104.
- **Correctness requires issuance to succeed before presentation runs.** The experiment asks for the event σ ≠ ⊥ ∧ b = 1, since the paper defines presentation on credentials only.
- **No obligation theorem for `ExtractablePoly`.** The theorem asserting extractability for every scheme without premises was false and was removed (#177). The asymptotic clause of Theorem 5.10 is #148.
- **Anonymity game at fixed setup, negligibility over instance families.** The games take the crs, the keys, the attributes, the predicate and the initial table as parameters, as Definition 4.4 quantifies pointwise, since a game that samples setup bounds an average and an average does not bound every crs.
- **The issuer adversary runs before and after the user's request**, with random-oracle access in both runs, so that a simulator that reprograms the oracle at its first move is detectable.
- **Two adversary structures, not one pair.** A and D are separate, as the statistical and everlasting variants of Definition 4.4 constrain them separately.
- **The anonymity simulator runs in the random-oracle state monad**, so it may reprogram the table, the power §3.3 grants a simulator.
- **The Present oracle answers under the queried predicate** φ′, the printed φ being read as a typo.
- **The extractor of Definition 4.5 takes the random-oracle table** as of the call and runs in `ProbComp`, since the proof of Theorem 5.10 builds it from the proof systems' extractors, which read the trace.

**The MAC and its reductions, §5.3.**

- **Conditioned sign masks** and **conditioned η masks.** The reduction's masks are sampled conditioned on Uⱼ ≠ 0 and on H ≠ 0, since the real game draws both from the nonzero elements and the game equalities of Lemma 5.4 are false otherwise.
- **Claim 5.7, the n → 1 collapse translates representations** (A5), and **the collapse direction is uniform in all n coordinates**, where the paper fixes z₁ = 1, at the same 1/p and with no distinguished index.
- **`WellBehaved` and the translation to the plain game.** *Superseded.* The first encoding of the algebraic group model gated each query on a consistent representation and needed the hypothesis `WellBehaved` at every key, which also rejected every Help query. Issue #235 replaces it by an adversary type that submits coefficients only, with a forget map into the game with Help and a transfer lemma without side condition. PR 246 deletes the bridge, PR 247 restricts the MAC game, parts 3 to 7 follow. Semar's report gives the timeline and the cost, four merged PRs reverted.
- **Theorem 5.10 at the honest UF-CMVA game with Help.** The unforgeability term of Theorem 5.10 is the advantage in the honest Figure 5 game with the oracle Help answered by the challenger, since the proof of Theorem 5.10 uses Help's answer and the paper ties Help to no model (#243).

**Anonymity of μCMZ, §5.4.**

- **Theorem 5.8 at a fixed crs.** The §3.3 advantages in the bound are taken on views that fix the crs at the H of the anonymity game, since a pointwise advantage is not bounded by sampled ones in general.
- **The anonymity simulator takes a trace extractor**, a function of the crs, the statement, the proof and the table, since Definition 4.4 puts ∃Sim before ∀A and the simulator cannot depend on the adversary a `KSNDExtractor` takes.

**One-more unforgeability and the anonymous token, §5.6 and §5.2.**

- **Exact-length representations in the AGM OMUF game.** A representation is accepted only with one coefficient per issued pair, so it evaluates the same against any later transcript. A simplification, not a soundness requirement, with three alternatives recorded.
- **Theorem 5.11 stated before its reductions exist.** The reductions are definitions with `sorry` bodies at the whole function type, named in the bound. Existential reductions are vacuous at a fixed group, a uniform ε on every discrete-log adversary is false or trivial, and `sorry` under the binders makes f A₁ = f A₂ hold by `rfl`. Claims 5.12 and 5.13 each name their own reduction, and the theorem's is their mixture.
- **One-more forgers have a private coin oracle.** The forger the lifting lemma builds samples a random-oracle cache and simulator runs, which a coinless type cannot express (#232).
- **Two carriers for one-more unforgeability.** The core and Figure 6 at `ProbComp`, the scheme with π_is at the oracle carrier with its own game run through one `runRO`, one experiment `omufExp` generic in the carrier, and a bridge equating the lifted advantage with the `ProbComp` one (#183).
- **Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11.** *On the branch.* Correctness, Definition 4.4 anonymity on the token as a credential with the Theorem 5.8 simulator minus its π_iu part and without the Remark 5.9 hypotheses, and one-more unforgeability with the Theorem 5.11 bound plus the π_is term. The clause on the branch is on the plain game of Figure 6 and quantifies over every adversary, which claims more than the paper proves. The decision of 28 October is to state it in the algebraic group model as printed, which needs a game in that model for the scheme with π_is, of the size of #181, so #184 is postponed.

**Open.**

- **The crs and the group** (#148). The instance fixes the group and the generator as type parameters, so every theorem is an inequality at one group, with no λ. The λ-indexed family is the committed step, and until it exists the asymptotic predicates are not provable for μCMZ.
- **Adversary classes and the paper's p.p.t. class** (#240). Every adversary is an `OracleComp` computation with no running time. Under "for all adversaries" the wider class strengthens a theorem, under "there exists a simulator" it weakens a definition. The one-more forgers contain the paper's class since #232. The UF-CMVA forgers, the extractors and the efficiency parameters are unclassified.

## Part B. Lessons the record supports

1. **A bound term without a reduction has nowhere to come from.** The printed Adv^dl of Lemma 5.4 (item 2) and the missing gap-DL term of Theorem 5.1 (item 6) appeared when the statement had to name a reduction for each summand.
2. **An existential reduction at a fixed group proves nothing.** A perfect discrete-log solver exists on a finite group, so "there exists B" is vacuous and "every adversary has advantage at most ε" is false or trivial. Every statement names its reduction (DA *Theorem 5.11 stated before its reductions exist*).
3. **Ask "what if it is zero" of every sampled or received value**, in the scheme and in the reduction. It gave items 8, 13, 14 and P22 on the scheme side and the two conditioned-mask entries on the reduction side, where a game equality is false until the reduction excludes the same zero the game excludes.
4. **One proof may analyze a smaller scheme than the theorem names.** Figure 9, Theorem 5.3 and the proof of Theorem 5.11 describe three schemes (item 7). The way out was to state the smaller scheme under its own name, prove the printed bound for it, and pay the difference in a separate lemma.
5. **Summary theorems drift from the proved ones across revisions.** Items 17 to 19 are all copies that were not updated. Derive the overview statement from the proved theorems, and read the version history.
6. **A ∀-quantified semantic hypothesis on the adversary is a sign of a modelling error.** `WellBehaved` quantified over every key, excluded the Help oracle that a downstream proof needs, and nothing proved it was the paper's notion of an algebraic adversary. The type should make misbehaving unrepresentable, so the transfer lemma has no side condition (#235).
7. **The adversary's type is part of the theorem.** Coins (#232), the Help oracle (#243) and the encoding of the algebraic group model each changed which forgers a bound covers, and each was decided when a downstream proof needed a forger the type could not express.
8. **The order of quantifiers decides what a simulator may see.** ∃Sim before ∀A forces a trace extractor (DA *The anonymity simulator takes a trace extractor*), and an oracle adversary that queries at any time forces two runs of the issuer (DA *The issuer adversary runs before and after the user's request*).
9. **Pointwise and sampled quantifiers need a bridge.** Definition 4.4 quantifies over every crs, the §3.3 games sample it, and an average does not bound every point (DA *Anonymity game at fixed setup*, *Theorem 5.8 at a fixed crs*). The fixed group is the same question one level up (#148).
10. **A fidelity claim quotes the paper, and where the paper is silent the choice is recorded as a choice.** Every entry of the design record carries the page it rests on or says that the paper leaves the point open (#240).
11. **The paper is the source of truth, and a problem in it is fixed mathematically.** When the code base lacks the game a theorem needs, the game is built, and the theorem is not restated over the game at hand (DA *Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11*, #184).
12. **Every departure gets an entry with a date and an owner, and goes upstream early.** Item 7 went to Rolfe on 20 August with a proposed correction. When the same question returned two months later, the π_is variant and the game carrier, the entry answered it.
