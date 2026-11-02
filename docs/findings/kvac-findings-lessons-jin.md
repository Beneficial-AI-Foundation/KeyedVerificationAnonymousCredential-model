# Findings and lessons from Jin
> This is based on the process of formalizing Theorem 5.3 track and the reviews done.

## Part A. Findings about the paper

### A1. Bounds that are too small or hide a term (the proofs are right, the constants are not)

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 1 | "The 1/p non-vanishing bound should be 3/p (p. 38)" | "except with probability 1/p" for a degree-3 polynomial. Schwartz–Zippel gives 3/p. | Lemma 5.4 track, sharpened in the review of the AGM series |
| 2 | "Lemma 5.4's printed Adv^dl summand has no reduction behind it (pp. 36–38)" | The statement has an Adv^dl term, but the proof never shows how it is introduced. It builds one reduction, to 3-DL, and no DL reduction, so the term is unjustified slack. | Lemma 5.4 track |
| 6 | "Theorem 5.1's printed bound elides the gap-DL term" | The printed bound hides the gap-DL term that the proof of Lemma 5.5 actually uses. The faithful bound is Adv^3-dl + Adv^gap-dl + 5/p. | Lemma 5.5 track |
| 12 | "Claim 5.13's bound has no term for Verify queries (pp. 46–47)" | A forger that makes no Sign query and Q Verify queries learns x₀ + xᵣ with probability (Q + 1)/p and wins. The reduction extracts nothing from it. | Theorem 5.3 track (found while stating Claims 5.12 to 5.14) |

**Lesson.** Writing the reduction as a program forces every constant to be derived. Three of the four were caught because a Lean statement had to say exactly which event has which probability.

### A2. Typos in the equations

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 3 | "Eq. 13: X₀'s X-coefficient (typo)" | X₀'s coefficient in X drops a factor. | Lemma 5.4 track |
| 4 | "Eq. 14: signing-response coefficient (typo)" | The signing-response coefficient is wrong. | Lemma 5.4 track |
| 5 | "Claim 5.6's extraction has the wrong sign (p. 39)" | The extraction has the wrong sign. | Lemma 5.5 track |
| 9 | "Claim 5.6 never defines Xᵣ (p. 39)" | Xᵣ is used but never defined. | Lemma 5.5 track |
| 10 | "Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term (p. 39)" | The Verify query drops a term. | Lemma 5.5 track |
| 11 | "Claim 5.6's Verify query misplaces the inverse (p. 39)" | The inverse is on the wrong factor. | Lemma 5.5 track |

**Lesson.** None of these change the result, but each one stopped a proof until it was found. A reader of the paper would either fix them silently or miss them completely. With a machine every step is checked, so the moment a proof step does not match the theorem it claims to prove, the mismatch is visible and has to be resolved rather than read past.

### A3. The scheme in the figure is not the scheme in the proof

| Errata # | Errata section | What is wrong | Origin |
| --- | --- | --- | --- |
| 7 | "Figure 9 boxes only π_iu, but the Theorem 5.11 proof analyzes the scheme without π_is (pp. 34–35, 40, 44)" | Figure 9 removes only π_iu for the token variant, Theorem 5.3 keeps π_is, but the proof of Theorem 5.11 analyzes a scheme with neither proof. | Theorem 5.3 track, reported to the author in August 2026 |
| 8 | "Figure 9 writes ℤ_p where §5.1 and correctness need ℤ_p^× (pp. 33–34)" | The figure draws three scalars from ℤ_p where the prose needs ℤ_p^×. A zero draw makes an honest run fail. | Theorem 5.3 track |
| 13 | "Figure 9 samples H ←$ 𝔾, but §2.1.1 presents G and H as generators (pp. 11, 34)" | H = 0 is possible, and then anonymity is false. | crs sampling fix (#149, #216) |
| 14 | "Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0_𝔾 (pp. 40–41)" | The simulated U′ is 0 with probability 1/p, the real one never. | crs sampling fix (#149, #216) |
| 15 | "Sim.P's Z omits the xᵣU′ term (pp. 34, 40–41)" | The simulator's Z differs from the server's by xᵣU′. The simulator also needs Xᵣ in its state to add the term, found in the review of #216. | crs sampling fix (#149, #216), the state point from its review |

What we did about item 7. We formalized the scheme the proof actually analyzes, `μCMZATCore` with neither issuance proof, as the main lemma, and recorded a lifting lemma that adds one Adv^zk term to recover the printed theorem. This is a decision, not a fix, and it is written down in the design document.

**Lesson.** A figure, a theorem statement and a proof can describe three different schemes without anyone noticing. On paper the differences are carried over from one to the next with no visible consequence, because the reader fills the gaps with the intended scheme. A formalization cannot do that. It needs one precise scheme to define the game on, so it has to pick one and say so.

### A4. Things the paper leaves implicit that the formalization had to decide

These are not errors. They are places where the paper says less than a machine needs, and the choice is recorded in `docs/DESIGN_ALTERNATIVES.md` with a fidelity argument.

- **Fixed group instead of a λ-indexed family** (`docs/presentations/rolf-status/per-group-analysis.md`, and the "Open alternatives" paragraph *The crs and the group* in `DESIGN_ALTERNATIVES.md`). The paper states theorems over GrGen(1^λ). Every proof argues at one fixed group. We state every theorem as a concrete inequality at a fixed group, which is also what a deployment instantiates (Signal's ristretto255 gives 3/p ≈ 2^-250). The asymptotic version is a separate layer (#148).
- **Named reductions instead of "there exists an adversary"** (`DESIGN_ALTERNATIVES.md`, *Theorem 5.11 stated before its reductions exist*, and the note *Why named reductions* in the `OneMoreUnforgeability` module docstring). On a finite group a perfect discrete-log solver exists, so a statement of the form "there exists B with Adv(A) ≤ Adv(B) + c" is trivially true. Our theorems name the reduction they build.
- **Adversaries are programs with no running time** (issue #240, with the proposed entry *Adversary classes and the paper's p.p.t. class*). Every adversary is an `OracleComp`, wider than the paper's p.p.t. class. The rule we arrived at: under a "for all adversaries" quantifier a wider class makes the theorem stronger, under a "there exists a simulator or extractor" quantifier it makes the definition weaker, so simulators and extractors must be named or carry an efficiency predicate. The one real gap this exposed, the UF-CMVA forgers without a coin oracle, is now scheduled.
- **The AGM as a gate, not a type** (Lemma 5.4 track, refined in the review of #214; `DESIGN_ALTERNATIVES.md`, *`WellBehaved` and the translation to the plain game*). The instrumented oracle answers `false` to a lying representation, and the class of honest algebraic adversaries is a separate predicate `WellBehaved`. Our review found that quantifying it over all key configurations excludes forgers the paper covers, with a four-line counterexample, and the quantifier is being fixed.
- **Exact-length representations in the one-more game** (`DESIGN_ALTERNATIVES.md`, *Exact-length representations in the AGM OMUF game*). The paper's AGM representation is a list over "all elements received so far". We require exactly one coefficient per issued pair, so a representation can be read against any later transcript. Recorded with the three rejected alternatives.
- **Which queries count toward q** (the paragraph *Why the gate cannot strengthen the adversary* of the same entry, and the `OMUFGame` docstring). Every Sign query counts, refused ones included, and the budget is a hypothesis on the adversary, not a field of its type.
- **Help oracle in the MAC game** (Lemma 5.4 track; the `AlgebraicMAC.lean` module docstring and the blueprint node `agm_model`). The paper's proof gives the adversary a Help oracle "at no cost to the bound" because Theorem 5.11 needs it. The formal game has it from the start.

## Part B. Lessons from doing the work

### B1. On method

1. **State first, prove later, but anchor everything.** We put the statement of Theorem 5.11 and its three claims on `main` with `sorry` before any proof existed, each sub-lemma registered as a blueprint node. Reviews of a statement are cheap and catch the modelling errors (A3, A4) before proof effort is spent. The rule that made it safe: a milestone node is anchored only when all its declarations exist, never half.
2. **One tracker, computed from the code.** We retired the hand-maintained progress tool. The Verso blueprint, with a CI check that every public declaration is anchored in exactly one node, is the only status board. Hand-maintained tables drifted within weeks.
3. **Errata and design decisions are deliverables, not side notes.** Both files are part of every review. A PR that deviates from the paper without an entry is sent back.
4. **Public prose cites the paper, never our plan.** Docstrings and blueprint nodes reference O24 definitions, equations and pages. Issue numbers and plan labels stay in PR bodies, so the documentation survives the plan.
5. **Stacked PRs and squash merges do not mix without a rule.** After a squash merge every child branch conflicts. The rule `git rebase --onto main <old parent tip>` after each merge, one PR at a time, kept a six-PR stack moving.

### B2. On Lean and VCV-io

6. **Two programs that compute the same distribution are not equal.** `OracleComp` is a free monad, so equality of programs is syntactic. Correctness had to be stated on the output distribution or support, not on the programs. This shaped the whole correctness layer.
7. **Instance search is the main source of lost days.** A discrete-log helper had to be sealed `irreducible` because unfolding it in a polynomial-ring context sent typeclass search into a loop. Importing a library umbrella instead of the two modules needed turned a 2-minute CI into a 6-hour hang. The lesson is to import narrowly and to seal interfaces whose unfolding is never needed.
8. **The same term can be spelled two ways.** A lift inserted by a coercion and one written by hand elaborate with different instance terms. `rw` and `simp` then fail on a goal that prints identically, and only `erw` bridges it. Write the lift explicitly and factor the bridge into one lemma.
9. **Probability bookkeeping needs the right primitive.** Conditioning a sampler (masks nonzero, H nonzero) is a one-line change in the game and a new lemma for every proof that read the old distribution. Decide the sampling domains before the proofs, not after.

### B3. On reviewing

10. **A review is a walkthrough plus a counterexample.** Every correctness comment we post carries the smallest input that breaks the claim. Comments without one were the ones that got argued about.
11. **Two independent machine reviewers, blind to each other and to our draft.** Codex and Kimi review the same packet. Codex is strong on counterexamples and reuse, Kimi inflates severity and once read "no sorry in the body" as "proved". Every machine claim is checked at the source before it reaches a PR, and about a third are rejected.
12. **Parallel reviews with sub-agents work with two rules.** Each agent gets its own worktree and writes its final file before handing back, and the coordinator re-verifies the main claims. Six PRs were reviewed in one day this way. The agents did not resume by themselves after their reviewers finished, so the coordinator has to nudge them.
13. **Reviewing other tracks is where cross-cutting errors appear.** The adversary-class question (#240), the H = 0 consequences for the reductions, and the stale constants after a sampler change were all found by reviewing someone else's PR against our own files.

### B4. On working with the paper's author and with each other

14. **Report errata early and in the author's terms.** Item 7 went to the author in August with a proposed correction, not a bug report.
15. **Every decision gets a date and an owner in the design document.** When the same question came back two months later (the π_is variant, the game carrier), the entry answered it.
