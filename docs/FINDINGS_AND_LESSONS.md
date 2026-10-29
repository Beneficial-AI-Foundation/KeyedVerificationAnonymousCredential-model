# Findings and lessons from the repository record

This report merges the two files in which the project recorded its departures from the paper, the errata, `docs/presentations/rolf-status/errata.md`, with the discrepancies between the printed text and what the paper's own arguments require, and the design record, `docs/DESIGN_ALTERNATIVES.md`, with the decisions taken where the paper says less than a formalization needs. Both files stay in the repository with their full text, frozen, and receive no new items. This report is the record from now on, in the format of the team's reports of October 2026.

**How to add an item.** A new finding about the paper takes the next number of this file, counting through the tables of Part A in order, and goes into the table of its category, one row with that number, an empty errata column, a short heading with the page, what is wrong in one sentence, the Lean object that carries the correction, its kind, its status and its origin. Its full account, the printed text, why it is wrong, the proposed correction and where the formalization records it, goes in a paragraph below the table, headed by the number. A new design decision goes into Part A6 as one bullet under the layer of the paper it concerns, or under the item of Part A it answers, with the decision, the rejected alternative and the fidelity argument in full, and the date. A lesson that the record supports goes to Part B with the items or decisions it rests on. The status list and the "What we did" paragraphs are revised when a statement or a proof lands.

This is based on:

- `docs/presentations/rolf-status/errata.md`, items 1 to 17 on `main`, items 18 and 19 on the branch `microcmz-theorem-5-3` (#184),
- `docs/DESIGN_ALTERNATIVES.md`, 36 entries on `main` and one on that branch,
- the reports of Jin, Oana and Semar of October 2026 for the categories and the format only.

Paper: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552, cited as O24, in its version of 27 March 2026 unless a version is named. Items are numbered through the file in the first column of the tables, in order of appearance, and the prose refers to items by that number. The second column gives the number of the same item in the frozen `errata.md`, which the docstrings and the design record cite. "DA" abbreviates the design record, `docs/DESIGN_ALTERNATIVES.md`, so a reference of the form "DA *Conditioned η masks*" points at the entry of that file whose heading is *Conditioned η masks*, where the decision, the rejected alternative and the fidelity argument are written in full. **Kind** says whether an item lives only in the security argument (*proof*) or constrains an implementation (*impl*), as input for KVAC-verify. **Status** says where the item stands, on `main` or on a branch.

**Status of the formalization, theorem by theorem.**

- Theorem 1 is not stated. It is the conjunction of Theorems 5.2 and 5.3. Its μCMZ clauses can proceed while the anonymous token clause waits on Theorem 5.3.
- Theorem 5.1 is stated for algebraic adversaries in a form that excludes the Help oracle the paper adds after it, and its restatement for the game with Help is under review.
- Theorem 5.2 is not stated. Its two clauses are Theorems 5.8 and 5.10.
- Theorem 5.3 is stated on a branch and postponed until a game in the algebraic group model exists for the scheme with π_is.
- Lemma 5.4 is stated at n = 1, with the 3-DL reduction built, the Schwartz–Zippel bound 3/p proved and the coupling of the reduction with the real game in progress.
- Lemma 5.5 is stated. The n → 1 attribute collapse and the gap-DL reduction of Claim 5.6 are defined, their proofs open.
- Theorem 5.8 is stated with its simulator defined, the condition of Remark 5.9 as hypotheses, and its proof open.
- Theorem 5.10 has its game with Help merged, together with its extractor interface. Its setting is under review, its statement in draft.
- Theorem 5.11 is stated at n = 1 and for every n, for the core without π_is. Claims 5.12 to 5.14 are stated with their reductions named, the proofs open.

None of the findings of Part A, numbered below, weakens a result. The assumptions are the paper's own, with one addition, the condition of Remark 5.9 that the anonymity theorem takes as hypotheses (item 17). One unjustified summand is dropped (item 2). The additive constant of Theorem 5.1 goes from 3/p to 5/p, both about 2⁻²⁵⁰ at ristretto255. The Theorem 5.11 bound loosens by (q+3)/(p(p−1)) under the nonzero crs (item 14). One zero-knowledge term enters the one-more unforgeability bound (item 12). The overview bounds of Theorems 1 and 5.3 give way to the bounds of the theorems they summarize (items 17 to 19).

## Part A. Findings about the paper

### A1. Bounds and probabilities stated wrongly (the arguments are right, the constants or the relation are not)

| # | Errata # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 1 | The 1/p non-vanishing bound should be 3/p (p. 38) | The partial evaluation ψ of the forgery polynomial is nonzero "except with probability 1/p", without derivation. The polynomial ϕ has total degree 3, so Schwartz–Zippel gives 3/p, and whether a structural argument recovers 1/p is left open. | `agm_ufcmva_le_n1_explicit`, the term `3 * (card F)⁻¹` | proof | on `main` | Lemma 5.4 proof |
| 2 | 2 | Lemma 5.4's printed Adv<sup>dl</sup> summand has no reduction behind it (pp. 36–38) | The statement carries an Adv^dl term. The proof builds one reduction, to 3-DL, so the term is slack. | `agm_ufcmva_le_n1_explicit`, no DL term | proof | on `main` | Lemma 5.4 proof |
| 3 | 6 | Theorem 5.1's printed bound elides the gap-DL term | Lemma 5.5 sends the collision case to gap-DL, and the printed Theorem 5.1 bound drops that term. The formal bound is Adv^3-dl + Adv^gap-dl + 5/p. | `agm_ufcmva_le_explicit`, the Lemma 5.5 bound that Theorem 5.1 wraps | proof | on `main` | Lemma 5.5 statement (#209) |
| 4 | 12 | Claim 5.13's bound has no term for Verify queries (pp. 46–47) | A forger with no Sign query and Q < p Verify queries learns x₀ + xᵣ with probability (Q+1)/p, then wins whenever H ≠ 0. The reduction of Claim 5.13 extracts nothing from it. The bound needs a term of about Q/p, or the forger goes to the x₀ embedding of Claim 5.14. | module docstring of `OneMoreUnforgeability/Statements.lean` | proof | on `main` | Theorem 5.11 statements (#189) |

**What we did.** Every formal statement is an inequality on named reductions. Three bounds are stated.

- Lemma 5.4, one attribute. The paper prints Adv^3-dl + Adv^dl + 1/p. The formal bound is Adv^3-dl(B₁) + 3/p. The 3/p replaces the 1/p (item 1), and the Adv^dl term is gone (item 2).
- Lemma 5.5 and Theorem 5.1, n attributes. The paper prints Adv^3-dl + Adv^dl + 3/p. The formal bound is Adv^3-dl(B₁) + Adv^gap-dl(B_gap) + 5/p. The gap-DL term is the collision case of Claim 5.6 (item 3). The 5/p is the 3/p of Lemma 5.4 plus 1/p for the event Σᵢ Δᵢbᵢ = 0 of Claim 5.6 plus 1/p for the event x₁ = 0 of Claim 5.7.
- Theorem 5.11. The printed constants are kept, provisional until the constant audit of Track CMZ-OMUF, and item 4 is recorded as an obligation on the Claims.

The 3/p is the generic Schwartz–Zippel bound for a polynomial of degree 3. The design record leaves open whether a structural argument recovers the printed 1/p, which the paper does not derive (DA *Schwartz–Zippel bound 3/p, not the paper's 1/p*).

**Lesson.** A Lean statement must name every summand and the reduction behind it. A bound term without a reduction (item 2) has nowhere to come from, and a constant has to be derived (items 1, 3, 4). All four were caught because a statement had to say which event has which probability.

### A2. Typos in the equations

| # | Errata # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | 3 | Eq. 13: X₀'s X-coefficient (typo) | X₀'s X-coefficient drops the factor a₀. The correct coefficient is a₀b_h + b₀a_h. | `redTrace` | proof | on `main` | Lemma 5.4 coupling (#88) |
| 6 | 4 | Eq. 14: signing-response coefficient (typo) | Vⱼ's G-coefficient is a_{u,j}(a₀ + aᵣ + a₁mⱼ), not a_{u,j}(a_h a₀ + a_h + a₁mⱼ). | `reductionSignStep` | proof | on `main` | Lemma 5.4 coupling (#88) |
| 7 | 5 | Claim 5.6's extraction has the wrong sign (p. 39) | The extracted discrete logarithm has the wrong sign. | `gapDlReduction` | proof | on `main` | Lemma 5.5 (#208) |
| 8 | 9 | Claim 5.6 never defines X<sub>r</sub> (p. 39) | Xᵣ is used by the reduction and never defined. The key's constant part lacks xᵣ. | `gapDlKeyParts` | proof | on `main` | Lemma 5.5 (#207) |
| 9 | 10 | Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term (p. 39) | The Verify query subtracts zU alone where the full constant part cU must go. | `gapDlOracleImpl` | proof | on `main` | Lemma 5.5 (#207) |
| 10 | 11 | Claim 5.6's Verify query misplaces the inverse (p. 39) | The inverse applies to V alone instead of V − cU. | `gapDlOracleImpl` | proof | on `main` | Lemma 5.5 (#207) |
| 11 | 16 | Hybrid H2 of Theorem 5.8 charges ZKP<sub>cmz.iu</sub> for the simulation of π<sub>p</sub> (p. 41) | Hybrid H2's displayed bound charges ZKP_cmz.iu where the simulated proof is π_p of ZKP_cmz.p. | `μCMZ_anonymity` | proof | on `main` | Theorem 5.8 statement (#10) |

**What we did.** Each correction is documented at its use site in the reduction, `redTrace` and `reductionSignStep` for Eqs. 13 and 14 (DA *Eq. 13*, *Eq. 14*), `gapDlReduction`, `gapDlKeyParts` and `gapDlOracleImpl` for Claim 5.6. The Verify query of Claim 5.6 is formalized as Ddh(d·U, V − c·U), which needs no inverse and covers d = 0 as well (item 10). Item 11 is charged to ZKP_cmz.p in `μCMZ_anonymity`.

**Lesson.** None of these changes a result, and each stopped a proof until it was found. Eqs. 13 and 14 surfaced when the coupling between the reduction and the real game would not close with the printed coefficients. A reader who fills in the intended value never sees them.

### A3. The scheme in the figure is not the scheme in the proof

| # | Errata # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 12 | 7 | Figure 9 boxes only π<sub>iu</sub>, but the Theorem 5.11 proof analyzes the scheme without π<sub>is</sub> (pp. 34–35, 40, 44) | Figure 9 removes π_iu only, Theorem 5.3 keeps π_is, and the proof of Theorem 5.11 analyzes the scheme with neither proof. | `μCMZATCoreSyntax`, `μCMZATSyntax`. `omufPiIsZKAdversary` on the branch | proof | on `main` | Theorem 5.3 track. Raised with Rolfe on 20 August |
| 13 | 8 | Figure 9 writes ℤ<sub>p</sub> where §5.1 and correctness need ℤ<sub>p</sub><sup>×</sup> (pp. 33–34) | Three scalars are drawn from ℤ_p where §5.1 needs ℤ_p^×. A zero draw makes an honest run fail, with negligible probability, so the figure still satisfies Definition 4.3 and the erratum is the inconsistency with the prose. | `uniformUnits` in `credIssueSrv`, `credIssueUsr₂`, `credPresentUsr`, `atIssueSrv`, `atIssueUsr₂` | impl | on `main` | Theorem 5.3 track (#146, #147, #206) |
| 14 | 13 | Figure 9 samples H ←$ 𝔾, but §2.1.1 presents G and H as generators (pp. 11, 34) | H ←$ 𝔾 admits H = 0, where a distinguisher holding sk wins with advantage above 1 − 4/p and Theorem 5.8 is false. | `setup` with `uniformNonzero` | impl | on `main` | #149, PR #216 |
| 15 | 14 | Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0<sub>𝔾</sub> (pp. 40–41) | The simulated U′ is 0 with probability 1/p, the real one never. | `μCMZAnonSimulator`, u′ ←$ ℤ_p^× | proof | on `main` | #149, PR #216 |
| 16 | 15 | Sim.P's Z omits the x<sub>r</sub>U′ term (pp. 34, 40–41) | Sim.P's Z lacks the term xᵣU′ that the server computes. The simulator needs Xᵣ in its state. | `μCMZAnonSimulator`, the term `u' • pp.2.1` | proof | on `main` | #149, PR #216 and its review |

**What we did about item 12.** The scheme the proof of Theorem 5.11 analyzes, with neither issuance proof, is stated under its own name, `μCMZATCore`, and Theorem 5.11 is stated for it. The scheme of Figure 9 with π_is is `μCMZATSyntax` at the oracle carrier (#183). A lifting lemma, the simulation hybrid that replaces each real π_is by a simulated one at the cost of one Adv^zk_cmz.is term, returns to the paper's scheme (#205). The Theorem 5.3 statement carries that term through a named reduction with a `sorry` body (DA *The μCMZ_AT core removes both issuance proofs, not only the boxed π_iu*, and *Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11* on the branch). Jin raised the item with Rolfe on 20 August, with this correction and the plan to build the core first. Rolfe acknowledged it. The team did not wait for the paper's correction.

**What we did about items 13, 14, 15 and 16.** The formalization draws the three scalars of Figure 9 from the nonzero elements with `uniformUnits`, so an honest run never fails. It draws the crs H from 𝔾^× in `setup`, so `H ≠ 0` is recovered from `mem_support_uniformNonzero` where a proof needs it (DA *Nonzero issuance nonces*, *Nonzero crs H ←$ 𝔾^×*). Item 13 notes the same mismatch for the tag base U of the base MAC, Figure 9 against Eq. (1). The simulator `μCMZAnonSimulator` samples u′ ←$ ℤ_p^× and sets U′ = u′G (item 15). It adds u′Xᵣ to Z, which then equals the server's Z (item 16). Item 14 is the finding with the largest consequence. At H = 0 a distinguisher holding sk wins with advantage above 1 − 4/p against every simulator, so Definition 4.4 fails for μCMZ. No simulator repairs it.

**Lesson.** A figure, a theorem statement and a proof can describe different schemes without anyone noticing, because a reader fills the gaps with the intended scheme. A formalization defines the game on one precise scheme, so it has to pick one and say so. Every sampler is a question, "what if it is zero", and the answer decides correctness (item 13), a security theorem (item 14) or a simulation step (items 15, 16).

### A4. The overview statements disagree with the proved theorems

| # | Errata # | Errata section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 17 | 17 | Theorem 1 prints Adv<sup>simex</sup> where Theorem 5.8 prints Adv<sup>ksnd</sup> (pp. 4, 40, 42) | Theorem 1 prints Adv^simex where Theorem 5.8 prints Adv^ksnd, and Remark 5.9's bridge covers Schnorr proofs alone. | `μCMZ_anonymity`, `ksndSimAdv_le_ksndAdv_of_domainSeparated` | proof | on `main` | Theorem 5.8 statement (#10) |
| 18 | 18 | Theorem 5.3 charges Adv<sup>zk</sup><sub>cmz.iu</sub> to a scheme without π<sub>iu</sub> (pp. 35, 40–41) | Theorem 5.3's anonymity bound charges Adv^zk_cmz.iu for a proof the token's user never sends. | `μCMZAT_anonymous_token` | proof | on the branch `microcmz-theorem-5-3` (#184) | Theorem 5.3 statement (#184) |
| 19 | 19 | Theorem 5.3 prints the one-more unforgeability bound of the October 2024 version (pp. 35, 43) | Theorem 5.3 prints the one-more unforgeability bound of the ePrint version of October 2024, which no version proves. | `μCMZAT_anonymous_token`, `omufBound` | proof | on the branch `microcmz-theorem-5-3` (#184) | Theorem 5.3 statement (#184) |

**What we did.** The formalization states the §5 theorems, with `sorry`, and derives the overview ones from them. The anonymity theorem keeps the printed Adv^ksnd of Theorem 5.8. It takes the condition of Remark 5.9 as hypotheses in four forms, each proof system, simulator and extractor confined to a region of the random-oracle domain, the regions pairwise disjoint. Hybrid H3 needs the condition since it extracts from a π_is produced after a simulated π_iu, which the knowledge-soundness game of §3.3 does not cover. Hybrid H2 needs it as well. The Remark is stated as the lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated` over any proof system, with an explicit region of the random-oracle domain for "the vector sizes mismatch". The Remark's own requirement, that simulated proofs "cannot be turned into proofs" of the other relation, has no formal counterpart. No call site discharges the hypotheses before the compiled Σ-protocols of #3 exist (DA *Theorem 5.8 with the printed knowledge-soundness term*). The Theorem 5.3 statement on the branch bounds anonymity by Adv^zk_cmz.p + Adv^ksnd_cmz.is, with the Theorem 5.8 simulator minus its π_iu part. It bounds one-more unforgeability by the Theorem 5.11 bound plus the π_is term. The ePrint history settled item 19. The version of 3 October 2024 printed the Theorem 5.3 bound. The revision of 24 February 2025 rewrote the proof of Theorem 5.11 into Claims 5.12 to 5.14 with a new bound, while Theorem 5.3 was never updated. Theorem 1 exists only from the version of 27 March 2026, which follows the revised Theorem 5.11.

**Lesson.** Theorems 1, 5.2 and 5.3 are overview copies of §5 results, stated first and proved later (p. 35). Copies drift when the originals are revised. A summary theorem is stated as the conjunction of the theorems it summarizes, each read on the scheme the summary names. The version history of the paper is part of the evidence.

### A6. Things the paper leaves implicit that the formalization had to decide

These are not errors. They are places where the paper says less than a machine needs. Each choice was recorded with the decision, the rejected alternative and the fidelity argument, which the design record holds in full for the entries below. The entries that answer an erratum are cited above. The rest follow, by the layer of the paper they concern.

**The proof-system layer, §3.3.**

- **Security-model-agnostic specification set aside.** The NIZKP object is the game-based §3.3 specification. The earlier typeclass with model-supplied relations `indist`, `produces` and `extracts` stays in the tree, unimported, since it abstracts away the computational content a §3.3 citation needs (#43).
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

- **Conditioned sign masks** and **conditioned η masks.** The reduction's masks are sampled conditioned on Uⱼ ≠ 0 and on H ≠ 0. The real game draws both from the nonzero elements, so the game equalities of Lemma 5.4 are false otherwise.
- **Claim 5.7, the n → 1 collapse translates representations, not only messages.** The Lemma 5.5 reduction runs against the game with representations, so it translates every coefficient list to the 1-attribute basis, `AGMRepr.collapseRepr` and `AGMRepr.linCombCollapse`, an obligation the paper does not have since its reduction plays the plain game. **The collapse direction is uniform in all n coordinates**, where the paper fixes z₁ = 1, at the same 1/p and with no distinguished index.
- **`WellBehaved` and the translation to the plain game.** *Superseded.* The first encoding of the algebraic group model gated each query on a consistent representation. It needed the hypothesis `WellBehaved` at every key, which also rejected every Help query. Issue #235 replaces it by an adversary type that submits coefficients only, with a forget map into the game with Help and a transfer lemma without side condition. PR 246 deletes the bridge, PR 247 restricts the MAC game, parts 3 to 7 follow.
- **Theorem 5.10 at the honest UF-CMVA game with Help.** The unforgeability term of Theorem 5.10 is the advantage in the honest Figure 5 game with the oracle Help answered by the challenger, since the proof of Theorem 5.10 uses Help's answer and the paper ties Help to no model (#243).

**Anonymity of μCMZ, §5.4.**

- **Theorem 5.8 at a fixed crs.** The §3.3 advantages in the bound are taken on views that fix the crs at the H of the anonymity game, since a pointwise advantage is not bounded by sampled ones in general.
- **The anonymity simulator takes a trace extractor**, a function of the crs, the statement, the proof and the table. Definition 4.4 puts ∃Sim before ∀A, so the simulator cannot depend on the adversary a `KSNDExtractor` takes. The §9 extractor also reads the algebraic representations, which the instantiation of #3 must carry in the proof or in the table.

**One-more unforgeability and the anonymous token, §5.6 and §5.2.**

- **Exact-length representations in the AGM OMUF game.** A representation is accepted only with one coefficient per issued pair, so it evaluates the same against any later transcript. A simplification, not a soundness requirement, with three alternatives recorded.
- **Theorem 5.11 stated before its reductions exist.** The reductions are definitions with `sorry` bodies at the whole function type, named in the bound. Existential reductions are vacuous at a fixed group. A uniform ε on every discrete-log adversary is false or trivial. A `sorry` under the binders makes f A₁ = f A₂ hold by `rfl`. Claims 5.12 and 5.13 each name their own reduction, the theorem's being their mixture.
- **One-more forgers have a private coin oracle.** The forger the lifting lemma builds samples a random-oracle cache and simulator runs, which a coinless type cannot express (#232).
- **Two carriers for one-more unforgeability.** The core and Figure 6 stay at `ProbComp`. The scheme with π_is runs at the oracle carrier with its own game, through one `runRO`. One experiment `omufExp` is generic in the carrier, with a bridge equating the lifted advantage with the `ProbComp` one (#183).
- **Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11.** *On the branch.* Three clauses. Correctness. Definition 4.4 anonymity on the token as a credential, with the Theorem 5.8 simulator minus its π_iu part, without the Remark 5.9 hypotheses. One-more unforgeability with the Theorem 5.11 bound plus the π_is term. The three `omufBound` reductions take the π_is simulator, with the Sign budget a hypothesis counted by `OMUFQueryRO.isSign`. The node of the printed theorem names no Lean declarations, citing the milestone node of the corrected statement per the honesty rule of `docs/BLUEPRINT_MAINTENANCE.md`. The clause on the branch is on the plain game of Figure 6 over every adversary, which claims more than the paper proves. The decision of 28 October is to state it in the algebraic group model as printed, which needs a game in that model for the scheme with π_is, of the size of #181, so #184 is postponed.

**Open.**

- **The crs and the group** (#148). The instance fixes the group and the generator as type parameters, so every theorem is an inequality at one group, with no λ. The λ-indexed family is the committed step, and until it exists the asymptotic predicates are not provable for μCMZ.
- **Adversary classes and the paper's p.p.t. class** (#240). Every adversary is an `OracleComp` computation with no running time. Under "for all adversaries" the wider class strengthens a theorem, under "there exists a simulator" it weakens a definition. The one-more forgers contain the paper's class since #232. The UF-CMVA forgers, the extractors and the efficiency parameters are unclassified.

## Part B. Lessons the record supports

1. **A bound term without a reduction has nowhere to come from.** The printed Adv^dl of Lemma 5.4 (item 2) and the missing gap-DL term of Theorem 5.1 (item 3) appeared when the statement had to name a reduction for each summand.
2. **An existential reduction at a fixed group proves nothing.** A perfect discrete-log solver exists on a finite group, so "there exists B" is vacuous and "every adversary has advantage at most ε" is false or trivial. Every statement names its reduction (DA *Theorem 5.11 stated before its reductions exist*).
3. **Ask "what if it is zero" of every sampled or received value**, in the scheme and in the reduction. It gave items 13, 14 and 15 on the scheme side. On the reduction side it gave the two conditioned-mask entries, where a game equality is false until the reduction excludes the same zero the game excludes.
4. **One proof may analyze a smaller scheme than the theorem names.** Figure 9 and Theorem 5.3 name the token with π_is, while the proof of Theorem 5.11 analyzes the core without it (item 12). The way out was to state the smaller scheme under its own name with the printed bound, then pay the difference in a separate lemma.
5. **Summary theorems drift from the proved ones.** Items 18 and 19 are copies that were not updated across revisions, item 17 a copy that changed a term. Derive the overview statement from the proved theorems, with the version history in hand.
6. **A ∀-quantified semantic hypothesis on the adversary is a sign of a modelling error.** `WellBehaved` quantified over every key. It excluded the Help oracle that a downstream proof needs. Nothing proved it was the paper's notion of an algebraic adversary. The type should make misbehaving unrepresentable, so the transfer lemma has no side condition (#235).
7. **The adversary's type is part of the theorem.** Coins (#232), the Help oracle (#243) and the encoding of the algebraic group model each changed which forgers a bound covers. Each was decided when a downstream proof needed a forger the type could not express.
8. **The order of quantifiers decides what a simulator may see.** ∃Sim before ∀A forces a trace extractor (DA *The anonymity simulator takes a trace extractor*). An oracle adversary that queries at any time forces two runs of the issuer (DA *The issuer adversary runs before and after the user's request*).
9. **Pointwise and sampled quantifiers need a bridge.** Definition 4.4 quantifies over every crs while the §3.3 games sample it, and an average does not bound every point (DA *Anonymity game at fixed setup*, *Theorem 5.8 at a fixed crs*). The fixed group is the same question one level up (#148).
10. **A fidelity claim quotes the paper. Where the paper is silent, the choice is recorded as a choice.** Every entry of the design record carries the page it rests on or says that the paper leaves the point open (#240).
11. **The paper is the source of truth. A problem in it is fixed mathematically.** When the code base lacks the game a theorem needs, the game is built. The theorem is not restated over the game at hand (DA *Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11*, #184).
12. **Every departure gets an entry with a date and an owner, then goes upstream early.** Item 12 went to Rolfe on 20 August with a proposed correction. When the same question returned two months later, the π_is variant and the game carrier, the entry answered it.
