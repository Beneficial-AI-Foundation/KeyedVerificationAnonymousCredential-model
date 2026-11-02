# Findings and lessons from Semar

This is based on:

- the Theorem 5.1 track:
  - Lemma 5.4 (n = 1, 3-DL): the sign coupling (#48, #151–#153, #156–#158, #161), the statement (#155) and the
    proof skeleton (#162, #170, #172–#174);
  - Lemma 5.5 (n → 1, Claims 5.6 and 5.7): #194, #195, #207–#209;
  - Theorem 5.1: #213, #214, #218, #220;
- the restricted algebraic adversaries stack, which replaces the `WellBehaved` form of
  Theorem 5.1 (#246 and #247 open, parts 3–7 to follow);
- our changes on the one-more unforgeability side:
  - the private coin oracle for one-more forgers (#232);
  - the oracle carrier (#233, #237);
  - μCMZ_AT with π_is at that carrier (#238);
- the review of #243 (the UF-CMVA game with Help).

Errata numbers refer to `docs/presentations/rolf-status/errata.md`. "#217 item N" refers to Oana's
proposed items. DA refers to an entry of `docs/DESIGN_ALTERNATIVES.md`. **Kind** says whether an
item lives only in the security argument (*proof*) or constrains an implementation (*impl*), as
input for KVAC-verify.

**Status on main.** The statements of Lemma 5.4 (`agm_ufcmva_le_n1_explicit`), Lemma 5.5
(`agm_ufcmva_le_explicit`) and Theorem 5.1 in its `WellBehaved` form
(`microCMZ_ufcmva_le_of_wellBehaved`, removed by #246) are on main. The blueprint reports their
proof status. The formal bound is
**Adv^ufcmva(A) ≤ Adv^3-dl(B₁) + Adv^gap-dl(B_gap) + 5/p**, where the paper prints
Adv^3-dl + Adv^dl + 3/p.

## Part A. Findings about the paper

### A1. Bounds

| # | Errata section / DA entry | What is wrong | Lean | Kind | Origin |
| --- | --- | --- | --- | --- | --- |
| errata 1 | "The 1/p non-vanishing bound should be 3/p (p. 38)"; DA *Schwartz–Zippel bound `3/p`, not the paper's `1/p`* | The forgery polynomial has degree 3, so Schwartz–Zippel gives 3/p. We have not shown 1/p false, only that the paper does not derive it. | `agm_ufcmva_le_n1_explicit` (`3 * (card F)⁻¹`) | proof | Lemma 5.4 proof |
| errata 2 | "Lemma 5.4's printed Adv^dl summand has no reduction behind it (pp. 36–38)" | The proof builds one reduction, to 3-DL. The Adv^dl term is slack. | `agm_ufcmva_le_n1_explicit` has no DL term | proof | Lemma 5.4 proof |
| errata 6 | "Theorem 5.1's printed bound elides the gap-DL term" | Lemma 5.5 sends the collision case to gap-DL, and the printed bound drops that term. Since Adv^dl ≤ Adv^gap-dl, writing dl understates the assumption. | `agm_ufcmva_le_explicit` (`gapDlogAdv (gapDlReduction gen A)`) | proof | Lemma 5.5 statement (#209) |
| errata 6 | same | Where 5/p comes from: 3/p (errata 1), 1/p for Σᵢ Δᵢbᵢ = 0 in Claim 5.6, 1/p for x₁ = 0 in Claim 5.7. | `agm_ufcmva_le_explicit` (`5 * (card F)⁻¹`) | proof | Lemma 5.5 statement |
| #217 item 19 (Oana) | "Lemmas 5.4 and 5.5 are stated with '='" | Our part: every formal statement is an inequality on a named reduction. | `agm_ufcmva_le_n1_explicit`, `agm_ufcmva_le_explicit` | proof | Oana's Lemma 5.5 proofs document (#212) |

**Lesson.** The 5/p and the gap-DL term exist because a Lean statement must name every summand
and the reduction behind it. A bound term without a reduction (errata 2) has nowhere to come from.

### A2. Typos in the equations

| # | Errata section / DA entry | What is wrong | Lean | Kind | Origin |
| --- | --- | --- | --- | --- | --- |
| errata 3 | "Eq. 13: X₀'s X-coefficient (typo)"; DA *Eq. 13* | The printed coefficient drops a₀. The correct one is a₀b_h + b₀a_h. | `redTrace` | proof | Lemma 5.4 coupling |
| errata 4 | "Eq. 14: signing-response coefficient (typo)"; DA *Eq. 14* | Vⱼ's G-coefficient is a_{u,j}(a₀ + a_r + a₁mⱼ), not a_{u,j}(a_h a₀ + a_h + a₁mⱼ). | `reductionSignStep` | proof | Lemma 5.4 coupling |
| DA only | DA *Eq. 14: the simulated signing response* | Eq. 14 gives Verify only (X, X′), "as the maximum degree … is 2". The verification polynomial has degree 3, so Verify needs X″, as Help does. | `exponentEval` | proof | Lemma 5.4 coupling |
| errata 5 | "Claim 5.6's extraction has the wrong sign (p. 39)" | The printed value is −x. | `gapDlReduction` | proof | Lemma 5.5 (#208) |
| errata 9 | "Claim 5.6 never defines Xᵣ (p. 39)" | x_r is missing from pp and from the Sign, Verify and Help answers. | `gapDlKeyParts` | proof | Lemma 5.5 (#207) |
| errata 10, 11 | "Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term", "… misplaces the inverse (p. 39)" | The DDH query must remove the full constant part c·U, and the inverse applies to V − cU. Lean queries Ddh(d·U, V − c·U), which needs no inverse and also covers d = 0. | `gapDlOracleImpl` | proof | Lemma 5.5 (#207) |

**Lesson.** Eq. 13 and Eq. 14 were found because the coupling between the reduction and the real
game failed until the coefficients were right. A reader who fills in the intended value never
sees them.

### A3. Distribution conventions the proof needs but does not state

| # | DA entry | What the paper leaves out | Lean | Kind | Origin |
| --- | --- | --- | --- | --- | --- |
| DA | *Conditioned sign masks.* | The real U is uniform on 𝔾^× (Eq. 1) and Verify rejects U = 0. Eq. 14's "identically distributed" holds only when the sign masks are conditioned on Uⱼ ≠ 0. | `reductionMaskSample` | **impl**: sample U ≠ 0, verifier rejects U = 0 | Lemma 5.4 (#48) |
| DA | *Conditioned η masks* | After #216 (Oana) draws H from 𝔾^×, Lemma 5.4's game equality `AGM_UF_CMVAGame_evalDist_eq` is false unless the η masks are conditioned on H ≠ 0. | `redTrace` via `reductionMaskSample` | **impl**: setup rejects H = 0 | #229 |
| DA | *Claim 5.7: the collapse direction is uniform in all `n` coordinates* | The paper fixes z₁ = 1. Lean samples r⃗ uniformly in all n coordinates, at the same 1/p (x₁ = 0), with no distinguished index. | `nTo1Adversary`, `microCMZN3DLReduction` | proof | Lemma 5.5 (#195) |

**Lesson.** Each "what if it is zero" question about a sampled value (Oana's lesson 2) has a
counterpart in the reduction. The reduction's own masks must exclude the same zero the game
excludes, or a game equality fails.

### A4. A cross-reference that names the wrong theorem (candidate, not in errata.md)

The proofs of Lemmas 5.4 and 5.5 say that giving the adversary Help "will simplify the proof of
Theorem 5.11" (p. 36, p. 38). The only proof that uses Help's answer is Theorem 5.10,
extractability: p. 42 assumes the candidate Z can be checked through Help, and p. 43 uses Help's
answer for the first equality of its display. The proof of Theorem 5.11 (pp. 43–47) never mentions
Help. We raised it in our review of #243, and it is now recorded in #243's DA entry *Theorem 5.10
at the honest UF-CMVA game with Help*. Kind: proof.

### A5. Modelling decisions, MAC side

- **Named reductions, not "there exists B"** (DA *Theorem 5.11 stated before its reductions exist*,
  rejected alternatives). At a fixed group a perfect discrete-log solver exists, so ∃B makes any
  bound vacuous. Our first Theorem 5.1 had this form. Every statement now names `B₁` and `B_gap`.
- **One fixed group, not GrGen** (DA *Open alternatives*, #148). Every bound is an inequality at
  one group.
- **Theorem 5.1 with Help.** The paper proves the stronger claim with Help (p. 35), and Theorem
  5.10 consumes it. The game with Help is #243 (Christiano). The stack of PRs for issue #235
  states Theorem 5.1 for it. See Part B.
- **Coins.** The AGM UF-CMVA forgers have no coin oracle, so the Theorem 5.1 bounds cover the
  paper's deterministic algebraic forgers (#240, Christiano). The forger of the game with Help has
  a private coin oracle (#243).

### A6. Modelling decisions, one-more unforgeability side (our changes)

- **One-more forgers have a private coin oracle** (#232, DA of that name). The plain forger runs
  in `unifSpec + OMUFOracleSpec`, the algebraic one in `unifSpec + AGMOMUFOracleSpec`. The forger
  that the π_is lifting lemma (#205) builds samples a random-oracle cache and a simulator run, so a
  coinless type could not express it. The algebraic forger got the oracle too: a sampling plain
  forger can be the image of an algebraic forger only if the algebraic forger can sample.
- **Two carriers** (#233, #237, DA *Two carriers for one-more unforgeability*). The core μCMZ_AT
  and Figure 6 stay at `ProbComp`. A scheme with a Fiat–Shamir proof runs at `OracleComp (ZKRO H)`.
  Both games run one experiment, `omufExp`, and `omufAdvRO_lift` states that the lifted advantage
  equals the `ProbComp` one. #238 puts μCMZ_AT with π_is at that carrier, with its correctness.
- **Restricted algebraic one-more forger** (issue #235 stack parts 5–7, to follow). Jin's AGM OMUF game gated
  each query with `reprMatches` and an exact-length rule on the issued-pair coefficients. It left
  the bridge to the plain Figure 6 game as "the OMUF analogue of the MAC track's `WellBehaved`
  bridge (#81)". The new design changes three things:
  - The forger submits coefficients only, and a short or long list is normalized to the issued
    pairs on the way in.
  - A forget map `AGMOMUFAdversary.forget` with a transfer lemma `OMUFAdv_forget`, with no side
    condition, carries Theorem 5.11 to the plain Figure 6 advantage.
  - That is the advantage Theorem 5.11 is about (O24 p. 27, p. 43).

**Lesson.** The adversary's type is part of the theorem. Coins, Help and the encoding of the
algebraic group model each changed which forgers a bound covers. Each was decided only when a
downstream proof needed a forger the type could not express.

### Not yet in errata.md

- Eq. 14's Verify needs X″, since the verification polynomial has degree 3. This is in DA *Eq. 14*
  only; errata 4 covers the coefficient.
- The Help cross-reference names Theorem 5.11 where Theorem 5.10 uses it (A5).

## Part B. Our mistake: Theorem 5.1 stated with `WellBehaved`

### What we did

- **#73 (merged Jul 23).** The AGM game encoded the algebraic group model by gating. Verify and Help
  took group elements plus representations and answered `false` on a mismatch, and the win
  condition carried a consistency conjunct. That made Lemma 5.4 writable.
- **#213, #214, #218, #220 (merged Oct 9–16).** To reach the paper's game, we added:
  - a guarded oracle simulation (#213);
  - the predicate `WellBehaved` (#214);
  - a translation `toUFAdversary` to a plain Figure 5 adversary (#218);
  - the theorem `microCMZ_ufcmva_le_of_wellBehaved`: for every `WellBehaved` algebraic adversary,
    the plain Figure 5 advantage of its translation is bounded by the Lemma 5.5 bound (#220).
- **What `WellBehaved` asks.** At every key `sk`, crs `H` and parameters `pp`, the guarded run never
  fails and every reachable forgery is consistent. Its guard `agmGood` rejects every Help query, and
  the translation answers Help with `false`.

### Why it was wrong

1. **It formalized the printed theorem, not the one the proof establishes.** Theorem 5.1 is stated
   for Figure 5 (Sign and Verify), but the paper says "we actually will prove a stronger claim: the
   scheme is unforgeable even if the adversary is given one additional oracle Help" (p. 35), and
   both lemma proofs repeat it (pp. 36, 38). `WellBehaved` excludes every adversary that queries
   Help, so our theorem said nothing about the stronger claim.
2. **The downstream proofs could not use it.**
   - *Theorem 5.10 (extractability, Christiano, #179).* This is the real consumer of Help: its
     proof uses Help's answer (pp. 42–43). His #242 and #243 record that "`WellBehaved` forbids
     `Help` queries", so a bound for the game with Help was missing.
   - *The one-more side.* Jin's OMUF game was gated in the same way, and its bridge to Figure 6 was
     deferred as "the OMUF analogue of the MAC track's `WellBehaved` bridge (#81)". Chaining
     Theorem 5.11 into Theorem 5.3 goes through the forger that the π_is lifting lemma (#205)
     builds. That forger samples coins. Under the gate, a `WellBehaved`-style hypothesis would have
     had to hold, at every key, for an algebraic forger behind it.
3. **It is a semantic condition on the adversary, not a type.** It quantifies over every
   `(sk, H, pp)`, not the values `setup` and `keygen` sample. No one discharges it for a concrete
   adversary, and nothing proved that it is the paper's notion of an algebraic adversary.

### Timeline and credits

| Date | Who | Where | What |
| --- | --- | --- | --- |
| Jul 22 | Semar | #81 | Opened the bridge issue. It records that gating, rather than restricting the adversary type, is a semantic change (from a Codex review of #73/#74), and lists "adding Help does not change the bound" as an obligation. The choice was deferred, not made. |
| Oct 13 | Christiano | review of #214 | `WellBehaved` "quantifies over every key, crs H and parameters, where Figure 5 samples them by setup and keygen", and "forbids Help queries, which the paper adds". |
| Oct 13 | Christiano | #236 | Asks for a proof that `WellBehaved` is the algebraic condition of Theorem 5.1, which the docstring claimed and nothing proved. |
| Oct 13 | Christiano | #235 | Proposes restricting the adversary type instead of gating: "The paper has no gate." |
| Oct 15–16 | Semar | #214, #218, #220 | Merged after review, with #236 referenced from the docstrings. |
| Oct 16 | Christiano | #240 | Without coins, the class of Lemmas 5.4, 5.5 and Theorem 5.1 "holds only the deterministic forgers of the paper". |
| Oct 23 | Semar | #235, #236 | Restriction adopted; #236 closed as not planned. |
| Oct 27 | Semar | #246, #247 | The 7-part restricted stack opened: part 1 deletes the bridge, part 2 restricts the MAC game. |

### The fix (#235; #246 and #247 open, parts 3–7 to follow)

- The algebraic adversary submits coefficients only, over the basis (g, H, X₀, X_r, X⃗, issued
  pairs), and the challenger evaluates them. The basis contains g, so the type excludes no group
  element. The gate, the consistency conjunct, `helpConsistent` and `WellBehaved` go.
- A forget map into Christiano's game with Help, plus a transfer lemma with no side condition,
  carries the AGM bound to the honest game. Theorem 5.1 is then stated in its stronger form, for
  the game with Help.
- The same move on the one-more side (A7).
- Part 1 (#246) deletes `AGMBridge.lean`, `UFCMVA.lean` and `Core/SimulateQGuarded.lean`: 11 files,
  +45 −567.

### Cost

- Four merged PRs (#213, #214, #218, #220) are reverted by #246.
- The gate also cost inside Lemma 5.5. The 1-attribute oracle could re-check only the r⃗-weighted
  sum of the Help representations, which is weaker than the per-attribute check. So the n → 1
  collapse needed its own `helpConsistent` pre-check, which part 2 (#247) removes.

### Lessons

1. **Read what the proof proves and who uses it, not only the boxed statement.** The stronger claim
   was one paragraph after Theorem 5.1, and Theorem 5.10 consumes it.
2. **A risk you have written down is still a risk.** #81 named the gate-vs-type choice in July. We
   built four PRs on the gate before deciding it.
3. **A ∀-quantified semantic hypothesis on the adversary is a smell.** If the bound needs "the
   adversary behaves", the type should make misbehaving unrepresentable. Then the transfer lemma has
   no side condition and nobody has to discharge one.
4. **Statement-first review checks fidelity to the printed statement.** That is why it could not
   catch this. The review that did catch it read the statement against the paper's proof and
   against a downstream track.

## Part C. Lessons from doing the work

1. **The formalization found errors by refusing to type-check or couple, not by re-reading.**
   - Eq. 13 and Eq. 14 surfaced when the sign coupling would not close.
   - 3/p appeared when Schwartz–Zippel had to be instantiated on a degree-3 polynomial.
   - After #216 made H nonzero, Lemma 5.4's game equality became false until the η masks were
     conditioned the same way (#229).
2. **An existential reduction at a fixed group proves nothing.** Our first, unmerged Theorem 5.1
   bounded the advantage by an existentially quantified 3-DL and DL adversary. A brute-force solver has advantage 1 on a finite group,
   so the statement was vacuous. Every statement now names its reduction (A6).
3. **A warm editor is not a build.** A lemma with `glog ↑U` (the discrete log of a subtype
   coercion) in a kernel-checked term looked proven in the editor. It hung a cold `lake build` for
   hours, because `maxHeartbeats` does not bound the kernel. Since then, "proved" means a cold
   `lake build` plus `#print axioms`, never the editor's word.
4. **Instance search cost more days than mathematics.** Three examples:
   - A `SubtractionCommMonoid F` diamond through `PrimeOrderGroup`'s `AddCommGroup` projection made
     a cold build hang for 600 s and more; one `attribute [instance 50]` brought it to 15–20 s.
   - A bare `simp` on `Pr[… | $ᵗ(Fin n → F)]` loops.
   - So does a `SampleableType` instance for `{u : F // u ≠ 0}` found by search, fixed by an
     explicit instance.

   We also moved pure field lemmas into a leaf file that imports only VCV-io, where they elaborate
   normally instead of stalling for minutes.
5. **Definitionally equal is not reducibly equal.** After the v4.30 bump, `simp` stalled on binds whose type arguments differ only up to unfolding
   (an oracle `Range` versus `G × G`). Term-mode `bind_assoc`, `map_bind` and `bind_congr`, which
   unify at default transparency, closed them. Jin's lesson 8 is the same phenomenon at a lift.
6. **Carving a monolith branch into smaller, reviewable PRs is real work, and git loses things silently.**
   - A merge during the generator port dropped a ~689-line gap-DL block with no conflict. It showed
     up only as cascading "unknown identifier" errors.
   - `git rebase --update-refs` moved backup branches that sat inside the rebased range.
   - Since then: tip SHAs are recorded before every rebase, and `git range-diff` is read after.
7. **Reviews across tracks found what our own track could not.** Christiano's review of #214 and
   his #235 found the `WellBehaved` problem (Part B). Our review of #243 found the paper's Theorem
   5.11 cross-reference (A5).
8. **AI assistance works with guardrails, and only with them.** Agent and review claims were wrong
   often enough to need checking:
   - a reviewer's "this does not compile" (`__ := src` does compile on v4.30);
   - a claimed `IsUniformSpec (ZKRO H)` instance, which does not exist.

   The rules we kept: test each claim on the toolchain, run the axiom audit after a cold build, read
   every `git diff` before a commit, and never let an agent push.
