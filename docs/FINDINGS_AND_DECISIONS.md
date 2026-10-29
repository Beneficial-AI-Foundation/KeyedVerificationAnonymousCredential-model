# Findings about the paper and decisions of the formalization

Paper: Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint
[2024/1552](https://eprint.iacr.org/2024/1552), cited as O24, in its version of
27 March 2026 (`docs/Orru_2024.pdf`), unless a version is named.

This file joins two records that the project kept apart. The errata,
`docs/presentations/rolf-status/errata.md`, hold the discrepancies between the
paper's printed text and what its own arguments require, each checkable by hand
against the paper. The design record, `docs/DESIGN_ALTERNATIVES.md`, holds the
decisions where the paper says less than a formalization needs and an
alternative was rejected for fidelity, each with the decision, the rejected
alternative and the fidelity argument. Part A has the findings about the paper
in the five categories of the team's reports of October 2026, each item with
the formalization decision it led to. Part B has the decisions that answer no
error of the paper, grouped by the layer of the paper they concern. Every item
and entry is copied from its source. The index tables and the one-line
summaries are new.

**How to read an item.** *Status* says where the item stands. "On `main`" is
the merged record. "Proposed on #217" are Oana's seven candidates of 3 October
from the Lemma 5.5 proofs document, awaiting review, numbered P16 to P22 here
with their numbers on #217, since items 16 and 17 of the merged errata took
those numbers first. "Proposed in Semar's report" are the two candidates of his
report of 28 October, S1 and S2, not yet on #217. "On the branch
`microcmz-theorem-5-3`" are items 18 and 19 and the entry on Theorem 5.3, written
on 28 October for issue #184 and not merged. *Kind* follows Semar's report.
"Proof" means the item lives in the security argument alone. "Impl" means it
constrains an implementation, the input KVAC-verify needs.

**None of the findings weakens a result.** The assumptions are the paper's own.
One unjustified summand is dropped (item 2), the additive constant of Theorem
5.1 changes from 3/p to 5/p, both about 2⁻²⁵⁰ at ristretto255, one
zero-knowledge term is added to the one-more unforgeability bound (item 7), and
the overview bounds of Theorems 1 and 5.3 are replaced by the bounds of the
theorems they summarize (items 17 to 19).

## Part A. Findings about the paper

### Index

**A1. Bounds and probabilities stated wrongly.** The arguments are right, the constants or the relation are not.

| # | Section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | The 1/p non-vanishing bound should be 3/p (p. 38) | The partial evaluation ψ of the forgery polynomial is nonzero "except with probability 1/p"; ϕ has total degree 3, so Schwartz–Zippel gives 3/p. | `agm_ufcmva_le_n1_explicit`, the term `3 * (card F)⁻¹` | proof | on `main` | Lemma 5.4 proof |
| 2 | Lemma 5.4's printed Adv<sup>dl</sup> summand has no reduction behind it (pp. 36–38) | The statement carries an Adv^dl term; the proof builds one reduction, to 3-DL, so the term is slack. | `agm_ufcmva_le_n1_explicit`, no DL term | proof | on `main` | Lemma 5.4 proof |
| 6 | Theorem 5.1's printed bound elides the gap-DL term | Lemma 5.5 sends the collision case to gap-DL, and the printed Theorem 5.1 bound drops that term. The formal bound is Adv^3-dl + Adv^gap-dl + 5/p. | `agm_ufcmva_le_explicit` | proof | on `main` | Lemma 5.5 statement (#209) |
| 12 | Claim 5.13's bound has no term for Verify queries (pp. 46–47) | A forger with no Sign query and Q Verify queries learns x₀ + xᵣ with probability (Q+1)/p and wins, and the reduction of Claim 5.13 extracts nothing from it. The bound needs a term in Q. | module docstring of `OneMoreUnforgeability/Statements.lean` | proof | on `main` | Theorem 5.11 statements (#189) |
| P19 | Lemmas 5.4 and 5.5 are stated with "=" (pp. 36, 38) | Lemmas 5.4 and 5.5 write Adv^ufcmva = Adv^3-dl + …; the adversary whose forgery has U* = 0 has advantage 0, so the relation is ≤, as Theorem 5.1 prints it. | `agm_ufcmva_le_n1_explicit`, `agm_ufcmva_le_explicit`, inequalities | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| P21 | Claims 5.6 and 5.7 state their failure probabilities backwards (p. 39) | Claims 5.6 and 5.7 attach 1/p to the event that holds with probability 1 − 1/p. The bounds are unaffected. | none | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |

**A2. Typos in the equations.** None changes a result, and each stopped a proof until it was found.

| # | Section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | Eq. 13: X₀'s X-coefficient (typo) | X₀'s X-coefficient drops the factor a₀; the correct coefficient is a₀b_h + b₀a_h. | `redTrace` | proof | on `main` | Lemma 5.4 coupling (#88) |
| 4 | Eq. 14: signing-response coefficient (typo) | Vⱼ's G-coefficient is a_{u,j}(a₀ + aᵣ + a₁mⱼ), not a_{u,j}(a_h a₀ + a_h + a₁mⱼ). | `reductionSignStep` | proof | on `main` | Lemma 5.4 coupling (#88) |
| 5 | Claim 5.6's extraction has the wrong sign (p. 39) | The extracted discrete logarithm has the wrong sign. | `gapDlReduction` | proof | on `main` | Lemma 5.5 (#208) |
| 9 | Claim 5.6 never defines X<sub>r</sub> (p. 39) | Xᵣ is used by the reduction and never defined; the key's constant part lacks xᵣ. | `gapDlKeyParts` | proof | on `main` | Lemma 5.5 (#207) |
| 10 | Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term (p. 39) | The Verify query subtracts zU alone where the full constant part cU must go. | `gapDlOracleImpl` | proof | on `main` | Lemma 5.5 (#207) |
| 11 | Claim 5.6's Verify query misplaces the inverse (p. 39) | The inverse applies to V alone instead of V − cU. | `gapDlOracleImpl` | proof | on `main` | Lemma 5.5 (#207) |
| 16 | Hybrid H2 of Theorem 5.8 charges ZKP<sub>cmz.iu</sub> for the simulation of π<sub>p</sub> (p. 41) | Hybrid H2's displayed bound charges ZKP_cmz.iu where the simulated proof is π_p of ZKP_cmz.p. | `μCMZ_anonymity` | proof | on `main` | Theorem 5.8 statement (#10) |
| P17 | Claim 5.7 omits x<sub>r</sub> (pp. 39–40) | Claim 5.7 runs A without Xᵣ and its verification equation has no xᵣ term, although the reduction's input has Xᵣ. | `nTo1Adversary` | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| P20 | Claim 5.6: dropped and mixed indices (typo, p. 39) | The extraction formula writes m* for m*ᵢ, and the Sign reply mixes mⱼ,ᵢ and mᵢ for one message. | none | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |

**A3. The scheme in the figure is not the scheme in the proof.** Samplers, proofs and simulator steps that differ between Figure 9, the prose and the proofs.

| # | Section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 7 | Figure 9 boxes only π<sub>iu</sub>, but the Theorem 5.11 proof analyzes the scheme without π<sub>is</sub> (pp. 34–35, 40, 44) | Figure 9 removes π_iu only, Theorem 5.3 keeps π_is, and the proof of Theorem 5.11 analyzes the scheme with neither proof. | `μCMZATCoreSyntax`, `μCMZATSyntax`; `omufPiIsZKAdversary` on the branch | proof | on `main` | Theorem 5.3 track; raised with Rolfe on 20 August |
| 8 | Figure 9 writes ℤ<sub>p</sub> where §5.1 and correctness need ℤ<sub>p</sub><sup>×</sup> (pp. 33–34) | Three scalars are drawn from ℤ_p where §5.1 needs ℤ_p^×; a zero draw makes an honest run fail. | `uniformUnits` in `credIssueSrv`, `credIssueUsr₂`, `credPresentUsr`, `atIssueSrv`, `atIssueUsr₂` | impl | on `main` | Theorem 5.3 track (#146, #147, #206) |
| 13 | Figure 9 samples H ←$ 𝔾, but §2.1.1 presents G and H as generators (pp. 11, 34) | H ←$ 𝔾 admits H = 0, where a distinguisher holding sk wins with advantage above 1 − 4/p and Theorem 5.8 is false. | `setup` with `uniformNonzero` | impl | on `main` | #149, PR #216 |
| 14 | Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0<sub>𝔾</sub> (pp. 40–41) | The simulated U′ is 0 with probability 1/p, the real one never. | `μCMZAnonSimulator`, u′ ←$ ℤ_p^× | proof | on `main` | #149, PR #216 |
| 15 | Sim.P's Z omits the x<sub>r</sub>U′ term (pp. 34, 40–41) | Sim.P's Z lacks the term xᵣU′ that the server computes; the simulator needs Xᵣ in its state. | `μCMZAnonSimulator`, the term `u' • pp.2.1` | proof | on `main` | #149, PR #216 and its review |
| P22 | Figure 9 samples U ←$ 𝔾, against Definition 3.1's correctness (pp. 25, 34) | μCMZ.M draws U ←$ 𝔾 while V rejects U = 0, so an honest MAC fails to verify with probability 1/p, against Definition 3.1. | `mac` with `uniformNonzero` | impl | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |

**A4. The overview statements disagree with the proved theorems.** Theorems 1, 5.2 and 5.3 copy bounds that §5 proves in another form.

| # | Section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| 17 | Theorem 1 prints Adv<sup>simex</sup> where Theorem 5.8 prints Adv<sup>ksnd</sup> (pp. 4, 40, 42) | Theorem 1 prints Adv^simex where Theorem 5.8 prints Adv^ksnd, and Remark 5.9's bridge covers Schnorr proofs alone. | `μCMZ_anonymity`, `ksndSimAdv_le_ksndAdv_of_domainSeparated` | proof | on `main` | Theorem 5.8 statement (#10) |
| 18 | Theorem 5.3 charges Adv<sup>zk</sup><sub>cmz.iu</sub> to a scheme without π<sub>iu</sub> (pp. 35, 40–41) | Theorem 5.3's anonymity bound charges Adv^zk_cmz.iu for a proof the token's user never sends. | `μCMZAT_anonymous_token` | proof | on the branch `microcmz-theorem-5-3` (#184) | Theorem 5.3 statement (#184) |
| 19 | Theorem 5.3 prints the one-more unforgeability bound of the October 2024 version (pp. 35, 43) | Theorem 5.3 prints the one-more unforgeability bound of the ePrint version of October 2024, which no version proves. | `μCMZAT_anonymous_token`, `omufBound` | proof | on the branch `microcmz-theorem-5-3` (#184) | Theorem 5.3 statement (#184) |

**A5. Proof steps missing or misdirected as printed.**

| # | Section | What is wrong | Lean | Kind | Status | Origin |
| --- | --- | --- | --- | --- | --- | --- |
| P16 | Claim 5.6's simulated Verify omits the U ≠ 0<sub>𝔾</sub> check (p. 39) | The simulated Verify of Claim 5.6 tests the equation only and omits the check U ≠ 0, so it answers 1 on (0, 0) where the real oracle answers 0. | `gapDlOracleImpl` | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| P18 | Claim 5.7 forwards messages but not algebraic representations (pp. 39–40) | The n → 1 reduction forwards messages and never the algebraic representations the 1-attribute game needs. | `AGMRepr.collapseRepr`, `AGMRepr.linCombCollapse` | proof | proposed on #217, awaiting review | Lemma 5.5 proofs document (#212) |
| S1 | Eq. 14 gives the Verify arm two powers where the degree needs three (p. 37) | Eq. 14 gives Verify the powers (X, X′) only, "as the maximum degree of the resulting polynomial is 2"; the verification polynomial has degree 3, so Verify needs X″ as Help does. | `exponentEval` | proof | proposed in Semar's report of 28 October, not yet on #217 | Lemma 5.4 coupling; design record, *Eq. 14* |
| S2 | Lemmas 5.4 and 5.5 send Help to Theorem 5.11, whose proof never uses it (pp. 36, 38, 42–43) | The proofs of Lemmas 5.4 and 5.5 say that Help "will simplify the proof of Theorem 5.11"; the proof that uses Help's answer is Theorem 5.10's, and the proof of Theorem 5.11 never mentions Help. | none | proof | proposed in Semar's report of 28 October, not yet on #217 | review of PR #243; design record, *Theorem 5.10 at the honest UF-CMVA game with Help* |

### A1. Bounds and probabilities stated wrongly

#### 1. The 1/p non-vanishing bound should be 3/p (p. 38)

*Status.* on `main`. *Kind.* proof.

The proof of Lemma 5.4 needs the affinely-substituted forgery polynomial to
stay nonzero. The paper (p. 38, after Eq. 16) asserts that the partial
evaluation ψ(χ) = ϕ(aₕ + χbₕ, a₀ + χb₀, …) "is still a non-zero polynomial
in ℤp[χ], of degree at most 3, except with probability 1/p".

The degree-3 claim is right; the probability constant is stated without
derivation and is too small. The bad event is that the hidden shift
(aₕ, a₀, aᵣ, a₁, a<sub>u,1</sub>, …) lands on a root of the nonzero
polynomial ϕ — in particular ψ ≡ 0 forces ψ(0) = ϕ(a⃗) = 0. And ϕ has total
degree 3: its top monomials come from
α<sub>v,j</sub>·uⱼ·(x₀+xᵣ+mⱼx₁)·(x₀+xᵣ+m*x₁), a degree-2 representation
term times the degree-1 key polynomial. Schwartz–Zippel over the uniform
shift therefore gives 3/p; a bare 1/p is the bound a degree-1 polynomial
would give.

**Formalization decision, from the design record, *Schwartz–Zippel bound `3/p`, not the paper's `1/p`*.**

**Decision.** The Eq. 16 root bound for the non-identity case of Lemma 5.4 is
`3/p`, established via Schwartz–Zippel on the *multivariate* verification
polynomial `ϕ` (see "The route taken" below). Unlike the other entries, the
rejected alternative here is the paper's own printed value — but it is not
shown to be wrong. The direct Schwartz–Zippel argument this file formalizes
only reaches `3/p`; whether the paper's `1/p` is itself achievable via a
sharper, structure-aware argument is left open (see "Not claimed tight"
below).

**Rejected alternative.** O24 Eq. 16 states the bound as `1/p`.

**Fidelity argument.** The paper invokes Schwartz–Zippel to bound `ψ ≡ 0`, and
for a degree-`d` polynomial that bound is `d/p`, not `1/p`. The `1/p` would be
immediate only for a degree-1 form; for the degree-3 verification polynomial the
bound Schwartz–Zippel gives is `3/p`. The deviation loosens the concrete additive
term (`1/p → 3/p`) but leaves the asymptotic bound, and hence the security
statement, unchanged.

*The route taken.* `ψ ≡ 0` implies `ψ(x + 1) = 0` in particular, and by
`AGMPoly.eval_affineSubst` that is `ϕ` evaluated at the real-log point shifted
by the `b`-side masks, `v ↦ (a v + x·b v) + b v` — the `C★` step
(`eval_shift_eq_zero_of_affineSubst_eq_zero`,
`AGMReduction/Coupling.lean`, branch `microCMZ-agmreduction-coupling`). For a
fixed `x` that shifted point ranges uniformly with the masks, so Schwartz–Zippel
applies to the *multivariate* `ϕ` of total degree `≤ 3` directly
(`card_filter_eval_eq_zero_le`, `probEvent_eval_shift_eq_zero_le`), giving
`3/p`.

*The route not taken.* The same `3/p` follows from the top-degree homogeneous
part: writing `ψ(χ) = ϕ(a + χ·b)`, the coefficient of `χ^d` in `ψ` (with
`d = totalDegree ϕ ≤ 3`) is exactly `ϕ_d(b)`, since only the degree-`d`
monomials of `ϕ` can reach `χ^d` and each contributes the product of its
`b`-masks. From `ϕ ≠ 0` we get `ϕ_d ≠ 0`, so `ψ ≡ 0 ⟹ ϕ_d(b) = 0` and
Schwartz–Zippel on the nonzero degree-`d` form gives `Pr_b[ϕ_d(b) = 0] ≤ d/p`.
Rejected as a *formalization* route only: it needs the top-homogeneous-component
extraction lemma and its coefficient identity, where `C★` is one rewrite off an
already-proven evaluation law.

Either way the `3` is `totalDegree_verifPoly_le`, the only rung of the Eq. 16
degree tower the `C★` route consults; `natDegree_affineSubst_le` bounds the
`RedLog.maskedRepr` polynomials fed to `exponentEval`, a different step. Both
rungs are documented at the head of the Eq. 16 section in `AGMPolynomial.lean`,
which also records why the at-most-3-roots bound extraction was once cited for is
neither needed — `recoverDlog_eq` requires only `ψ ≠ 0` and that the challenge
exponent is a root — nor formalized here.

*Not claimed tight.* `3/p` is the **generic** Schwartz–Zippel bound for a
degree-`≤ 3` polynomial, and nothing here rules out a sharper one. The event is
structured — `ϕ` is a verification polynomial, not an arbitrary cubic — so `1/p`
may well follow from that structure; we have not looked. What the paper is
missing is therefore the *justification* for `1/p`, not necessarily the value:
the deviation recorded above is to the bound we can prove, and it would be
narrowed, not contradicted, by a structural argument.

#### 2. Lemma 5.4's printed Adv<sup>dl</sup> summand has no reduction behind it (pp. 36–38)

*Status.* on `main`. *Kind.* proof.

Lemma 5.4 (p. 36) states the single-attribute bound as
Adv<sup>3-dl</sup> + Adv<sup>dl</sup> + 1/p. Its proof (pp. 36–38) builds
one reduction, to 3-DL: the public parameters and the signing responses are
embedded off the 3-DL instance (Eqs. 13–14), and the forgery is turned into a
root of the affinely-substituted polynomial ψ, which is the 3-DL solution.
No DL reduction appears, so the Adv<sup>dl</sup> summand is unjustified by the
proof and survives only as nonnegative slack. The formalized statement
(`agm_ufcmva_le_n1_explicit`) bounds the advantage by
Adv<sup>3-dl</sup> + 3/p, with the constant from item 1.

#### 6. Theorem 5.1's printed bound elides the gap-DL term

*Status.* on `main`. *Kind.* proof.

The printed bound is Adv<sup>3-dl</sup> + Adv<sup>dl</sup> + 3/p. The
paper's own proof of Lemma 5.5 case-splits on a collision event and sends the
collision branch to gap-DL via Claim 5.6 — so the assembled bound carries a
gap-DL advantage term that the printed theorem statement does not show. The
formalized target keeps it explicit:

&nbsp;&nbsp;&nbsp;&nbsp;Adv<sup>ufcmva</sup>(A) ≤ Adv<sup>3-dl</sup>(B₁) +
Adv<sup>gap-dl</sup>(B<sub>gap</sub>) + 5/p,

with 5/p = 3/p (item 1) + 1/p (the keygen-shear bad event x₁ = 0 in the
no-collision branch) + 1/p (the vanishing-denominator bad event in the
gap-DL branch). The paper's Adv<sup>dl</sup> term has no reduction behind it
in this proof plan; it survives only as nonnegative slack.

#### 12. Claim 5.13's bound has no term for Verify queries (pp. 46–47)

*Status.* on `main`. *Kind.* proof.

Claim 5.13 bounds item (ii), a forgery polynomial with a monomial in η, by
1/p + Adv<sup>dl</sup>, the 1/p covering the degenerate mask b = 0. Every honest
Verify answer tests the key: the query (0, (G, c·G)) is accepted iff
c = x₀ + x<sub>r</sub>. A forger that makes no Sign query, Q < p Verify queries
over distinct c and a final guess among the untested values therefore learns
x₀ + x<sub>r</sub> with probability (Q + 1)/p, and outputs the forgery
(0, (H, (x₀ + x<sub>r</sub>)·H)) over H, which wins whenever H ≠ 0. Item (ii)
then happens with probability (Q + 1)(p − 1)/p². The reduction of Claim 5.13
substitutes η := a + bχ into ϕ = η·(x₀ + x<sub>r</sub> − k) and finds the zero
polynomial at the run's key, so it extracts nothing. The printed bound needs a
term of about Q/p in the number Q of Verify queries, or the argument has to send
this forger to the x₀ embedding of Claim 5.14, which does extract from it. A
matter of the concrete bound only, since Q/p is negligible asymptotically. The
general shape, a monomial that is nonzero as a formal polynomial but whose
coefficient vanishes at the run's key, is the same for Claims 5.12 and 5.14.

#### P19. Lemmas 5.4 and 5.5 are stated with "=" (pp. 36, 38)

*Status.* proposed on #217, awaiting review. *Kind.* proof.

Both lemmas write Adv<sup>ufcmva</sup> = Adv<sup>3-dl</sup> + … . The advantage
is defined per adversary (p. 25), so the lemmas assert the equality for every
adversary, and one adversary suffices to falsify it: the adversary that outputs
a forgery with U* = 0<sub>𝔾</sub> never wins, since µCMZ.V rejects U = 0<sub>𝔾</sub>,
so its advantage is exactly 0, while the right-hand side is at least 1/p. A
reduction yields "≤", which is what Theorem 5.1 (p. 35) already states.
Documented in `docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md` as "Statement".

#### P21. Claims 5.6 and 5.7 state their failure probabilities backwards (p. 39)

*Status.* proposed on #217, awaiting review. *Kind.* proof.

Two sentences attach 1/p to the wrong event:

- Claim 5.6: "The equation is non-trivial with overwhelming probability 1/p".
  The equation derived from the collision is non-trivial iff Σᵢ Δᵢbᵢ ≠ 0, with
  Δᵢ = mⱼ,ᵢ − m*ᵢ, which holds with probability 1 − 1/p; 1/p is the probability
  that it is trivial.
- Claim 5.7: "Assuming X₁ ≠ 0G (which happens with probability 1/p)". With
  X₁ = x₁G and x₁ uniform, Pr[X₁ ≠ 0<sub>𝔾</sub>] = 1 − 1/p; 1/p is
  Pr[X₁ = 0<sub>𝔾</sub>].

In each case the printed 1/p is the probability of the complementary event,
which is exactly the 1/p term of the claim's bound, so the bounds are
unaffected; only the sentences are backwards. Documented in
`docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`, Remark "Both claims state
their failure probability backwards".

### A2. Typos in the equations

#### 3. Eq. 13: X₀'s X-coefficient (typo)

*Status.* on `main`. *Kind.* proof.

Eq. 13 defines the affine embedding of the public parameters off the 3-DL
instance (X, X′, X″). The paper prints X₀'s X-coefficient as
a<sub>h</sub>b₀ + b<sub>h</sub>. Expanding X₀ = x₀·H under the affine
substitution v ↦ a<sub>v</sub> + x·b<sub>v</sub> gives the X-coefficient

&nbsp;&nbsp;&nbsp;&nbsp;a₀b<sub>h</sub> + b₀a<sub>h</sub>,

i.e. the printed version drops the a₀ factor. The corrected coefficient is
documented at its use site in the reduction-core module under review
(PR #88, `AGMReduction/Core.lean`, docstring at the Eq. 13 embedding).

**Formalization decision, from the design record, *Eq. 13: X₀'s `X`-coefficient (O24 p. 37)*.**

**Decision.** The challenge embedding builds `X₀`'s `X`-coefficient as
`a₀·b_h + b₀·a_h` (`AGMReduction/Core.lean`, PR #88, the Eq. 13 block of
`redTrace`). Like the `3/p` entry above, the rejected alternative
here is the paper's own printed value rather than a formalization ambiguity —
but unlike that entry, this one is a definite error: the printed coefficient
breaks the identity `X₀ = x₀·H` outright (see the Fidelity argument below).

**Rejected alternative.** O24 Eq. 13 (p. 37) prints
`X₀ = a_h a₀ G + (a_h b₀ + b_h) X + b_h b₀ X'`.

**Fidelity argument.** `X₀ = x₀·H`, so `log_G X₀ = x₀·η`; under the affine
masking `v ↦ a_v + χ·b_v` that is
`(a₀ + χb₀)(a_h + χb_h) = a₀a_h + (a₀b_h + b₀a_h)χ + b₀b_h χ²`. The printed
`G`- and `X'`-coefficients match; the printed `X`-coefficient `a_h b₀ + b_h`
drops the `a₀` factor from the second term. The dropped factor is not
cosmetic: with the printed coefficient the embedded `X₀` is no longer `x₀·H`
for the masked `x₀`, so the simulated public parameters stop being identically
distributed to an honest signer's, and Eq. 14's tag — which does use the
correct key factor — becomes inconsistent with them. Also recorded as item 3
of `docs/presentations/rolf-status/errata.md`.

#### 4. Eq. 14: signing-response coefficient (typo)

*Status.* on `main`. *Kind.* proof.

Eq. 14 gives the simulated signing response's coefficient. The paper prints
the factor as a·uⱼ·(a<sub>h</sub>a₀ + a<sub>h</sub> + mⱼa₁); the correct
factor is

&nbsp;&nbsp;&nbsp;&nbsp;A = a₀ + a<sub>r</sub> + a₁mⱼ,

the key polynomial's constant part evaluated at the queried message. Also
documented at its use site in PR #88.

**Formalization decision, from the design record, *Eq. 14: the simulated signing response (O24 p. 37)*.**

**Decision.** The reduction's sign step gives `Vⱼ` the `G`-coefficient
`a_{u,j}·A` with `A = a₀ + aᵣ + a₁mⱼ` (`reductionSignStep`), and both the
verify and help arms evaluate in the exponent against all four powers
`(G, X, X', X'')` (`exponentEval`). Two corrections to the same equation's
paragraph, both on correctness grounds.

**Rejected alternative.** O24 Eq. 14 (p. 37) prints `Vⱼ`'s `G`-coefficient as
`a_{u,j}(a_h a₀ + a_h + a₁mⱼ)`; its Verify bullet gives that oracle only
`(X, X')`, "as the maximum degree of the resulting polynomial is 2".

**Fidelity argument.** `log_G Vⱼ = (x₀ + xᵣ + mⱼx₁)·uⱼ`, which under the
masking is `(A + χB)(a_{u,j} + χb_{u,j})` with `A = a₀ + aᵣ + a₁mⱼ` and
`B = b₀ + bᵣ + b₁mⱼ`; its constant term is `a_{u,j}·A`. The printed factor
instead carries the `η`-mask `a_h` — which belongs to `X₀`'s representation,
not to the key — and omits `aᵣ`, so it contradicts the `X`- and
`X'`-coefficients of the very same equation, which do print `(a₀ + aᵣ + a₁mⱼ)`
and `(b₀ + bᵣ + b₁mⱼ)`. On the degree: the represented verification check is
`keyPoly · α.toPoly`, a degree-1 key (`totalDegree_keyPoly_le`) against a
degree-≤2 representation (`totalDegree_toPoly_le`, degree 2 reached by the
`x₀η` and `uⱼ(x₀+xᵣ+mⱼx₁)` monomials), hence degree ≤ 3 and not ≤ 2 — so the
verify arm needs `X''` exactly as the help arm does. Also recorded as item 4
of `docs/presentations/rolf-status/errata.md`.

#### 5. Claim 5.6's extraction has the wrong sign (p. 39)

*Status.* on `main`. *Kind.* proof.

From a collision Σᵢ mⱼ,ᵢ(aᵢG + bᵢX) = Σᵢ m*ᵢ(aᵢG + bᵢX) the paper derives
(Σᵢ (mⱼ,ᵢ − m*ᵢ)aᵢ)G = (Σᵢ (mⱼ,ᵢ − m*ᵢ)bᵢ)X and returns
x = (Σᵢ aᵢ(mⱼ,ᵢ − m*ᵢ))(Σᵢ bᵢ(mⱼ,ᵢ − m*ᵢ))<sup>−1</sup>. Moving the X-terms
across flips their sign, so the relation is
(Σᵢ (mⱼ,ᵢ − m*ᵢ)aᵢ)G = −(Σᵢ (mⱼ,ᵢ − m*ᵢ)bᵢ)X and the printed value is −x.
The correct extraction is

&nbsp;&nbsp;&nbsp;&nbsp;x = (Σᵢ aᵢ(m*ᵢ − mⱼ,ᵢ))(Σᵢ bᵢ(mⱼ,ᵢ − m*ᵢ))<sup>−1</sup>,

documented at its use site (`gapDlReduction` in
`AGMReduction/GapDLReduction.lean`).

#### 9. Claim 5.6 never defines X<sub>r</sub> (p. 39)

*Status.* on `main`. *Kind.* proof.

The gap-DL reduction B of Claim 5.6 invokes the adversary with
pp = (Γ, (X₀, X<sub>r</sub>, X₁, …, X<sub>n</sub>)) but defines only
X₀ = zH and Xᵢ = aᵢG + bᵢX. The signing, Verify and Help answers all use the
key's constant part z + Σᵢ aᵢmᵢ with no x<sub>r</sub>, although the game's key
on m⃗ is x₀ + x<sub>r</sub> + Σᵢ mᵢxᵢ. The corrected reduction samples
x<sub>r</sub>, publishes X<sub>r</sub> = x<sub>r</sub>G, and uses the constant
part

&nbsp;&nbsp;&nbsp;&nbsp;c = z + x<sub>r</sub> + Σᵢ aᵢmᵢ,

documented at its use site (`gapDlKeyParts` and `gapDlOracleImpl` in
`AGMReduction/GapDLReduction.lean`).

#### 10. Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term (p. 39)

*Status.* on `main`. *Kind.* proof.

For Σᵢ bᵢmᵢ ≠ 0 the printed Verify answer is the bit of
Ddh(U, (Σᵢ bᵢmᵢ)<sup>−1</sup>V − zU). Its Σᵢ bᵢmᵢ = 0 branch checks
zU + Σᵢ aᵢmᵢU = V, and the signing answer uses (z + Σᵢ aᵢmᵢ)U, but the Ddh
argument subtracts only zU. With d = Σᵢ bᵢmᵢ the honest equation
V = (c + x·d)U needs the full constant part c·U removed (item 9 adds the
x<sub>r</sub> term).

#### 11. Claim 5.6's Verify query misplaces the inverse (p. 39)

*Status.* on `main`. *Kind.* proof.

The printed argument (Σᵢ bᵢmᵢ)<sup>−1</sup>V − zU applies d<sup>−1</sup> to V
alone. Solving V = (c + x·d)U for the DH value gives d<sup>−1</sup>(V − cU) =
x·U, so the query must be

&nbsp;&nbsp;&nbsp;&nbsp;Ddh(U, d<sup>−1</sup>(V − cU)).

The formalization avoids the inverse by querying Ddh(d·U, V − c·U), which
returns the same bit for d ≠ 0 and also subsumes the d = 0 branch
(`gapDlOracleImpl`, `AGMReduction/GapDLReduction.lean`).

#### 16. Hybrid H2 of Theorem 5.8 charges ZKP<sub>cmz.iu</sub> for the simulation of π<sub>p</sub> (p. 41)

*Status.* on `main`. *Kind.* proof.

Hybrid H2 (p. 41) replaces π<sub>p</sub>
by the output of the zero-knowledge simulator of ZKP<sub>cmz.p</sub>, and its
displayed bound reads
Adv<sup>H2</sup> ≥ Adv<sup>H1</sup> − Adv<sup>zk</sup><sub>ZKP<sub>cmz.iu</sub>,D′</sub>,
with the subscript of H1. The system whose zero knowledge the step uses is
ZKP<sub>cmz.p</sub>, as the statement of Theorem 5.8 (p. 40) prints it. The
statement `μCMZ_anonymity` in `Schemes/MicroCMZ/Anonymity.lean` charges the
second term to ZKP<sub>cmz.p</sub>.

#### P17. Claim 5.7 omits x<sub>r</sub> (pp. 39–40)

*Status.* proposed on #217, awaiting review. *Kind.* proof.

Claim 5.7 runs A on public parameters (X₀, X₁, …, X<sub>n</sub>), while
X<sub>r</sub> is missing, and its displayed verification equation
(U*, V*) = (U, x₀U + Σᵢ m*ᵢxᵢU) has no x<sub>r</sub> term, although the
reduction's own input is (Γ, H, X₀, X<sub>r</sub>, X₁). The n → 1 reduction
receives X<sub>r</sub> from its 1-attribute challenger and forwards it, so A
sees the full pp. Note that Claim 5.6 omits x<sub>r</sub> differently; that
case is item 9. Documented in `docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`,
Remark "x<sub>r</sub> is omitted throughout the printed proofs".

#### P20. Claim 5.6: dropped and mixed indices (typo, p. 39)

*Status.* proposed on #217, awaiting review. *Kind.* proof.

Two index slips:

- The extraction formula
  x = (Σᵢ aᵢ(mⱼ,ᵢ − m*))(Σᵢ bᵢ(mⱼ,ᵢ − m*))<sup>−1</sup> writes m* for m*ᵢ in
  both sums (its sign is wrong as well, which errata.md item 5 treats).
- The Sign reply V := (z + Σᵢ aᵢmⱼ,ᵢ)U + u(Σᵢ bᵢmᵢ)X writes the queried
  message as mⱼ,ᵢ in its first sum and as mᵢ in its second, although both sums
  are over the same message, the j-th query m<sub>j</sub>.

The correct forms are m*ᵢ in the extraction formula and mⱼ,ᵢ in both sums of
the Sign reply. Neither slip affects the argument. Documented in
`docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`, Remark "Claim 5.6 has a sign
error and a dropped index".

### A3. The scheme in the figure is not the scheme in the proof

#### 7. Figure 9 boxes only π<sub>iu</sub>, but the Theorem 5.11 proof analyzes the scheme without π<sub>is</sub> (pp. 34–35, 40, 44)

*Status.* on `main`. *Kind.* proof.

Figure 9 (p. 34) marks the user proof π<sub>iu</sub> as the part removed for
the anonymous-token variant μCMZ<sub>AT</sub>, and Theorem 5.3 (p. 35) keeps
the issuer proof π<sub>is</sub>, its bound carrying the knowledge-soundness
term of π<sub>is</sub> for the anonymity clause. The proof of Theorem 5.11
(p. 44) answers the Sign queries with the bare (U′, V′) and its bound has no
zero-knowledge term, so the scheme that proof analyzes carries neither
issuance proof. Removing π<sub>is</sub> from the theorem instead is not an
option, since the anonymity simulator (p. 40) verifies and extracts from it.

Proposed correction: keep π<sub>is</sub> in the scheme and add one
Adv<sup>zk</sup><sub>cmz.is</sub> term to the one-more unforgeability bound,
obtained from the π<sub>is</sub>-less core by a simulation hybrid (a lifting
lemma). The formalization states the core as `μCMZATCore`
(`Schemes/MicroCMZ/ATVariant.lean`, PR #147), the π<sub>is</sub>-carrying
variant as `μCMZATSyntax` (`Schemes/MicroCMZ/ATVariantPiIs.lean`, #183), and
the lifting lemma under issue #205. The Theorem 5.3 statement (#184) carries
the added term through the named reduction `omufPiIsZKAdversary`, which #205
defines.

Correspondence. Jin Xing Lim raised the item with Rolfe Schmidt on 20 August
2026 on the Signal Shot KVAC channel on Signal, with the correction above and
the plan to state the core under its own name, prove the printed Theorem 5.11
bound for it, add the π<sub>is</sub>-carrying instance and the lifting lemma
on top, and keep the blueprint node of the printed Theorem 5.3 without Lean
declarations until the paper is corrected. Rolfe Schmidt replied: "This is
good work, thank you! I expect as more papers are formalized these findings
will be common." The plan is followed except for the wait on the paper. The
instance and the lifting lemma proceed now, and the node of the printed
Theorem 5.3 cites a milestone node for the corrected statement. No report to
the author is on record.

**Formalization decision, from the design record, *The μCMZ_AT core removes both issuance proofs, not only the boxed π_iu*.**

**Decision.** The formalized anonymous-token scheme is the *core* with both
issuance proofs removed, and is named accordingly (`μCMZATCore`,
`ATVariant.lean`). The `π_is`-carrying variant is `μCMZATSyntax`
(`ATVariantPiIs.lean`), at the oracle carrier with its own game `OMUFGameRO`.
A lifting lemma bounding its one-more unforgeability by the core's plus one
zero-knowledge term for `ZKP_cmz.is` is deferred until the upstream erratum
settles; the printed Theorem 5.3 blueprint node stays unanchored meanwhile.

**Rejected alternatives.** (i) Formalizing the printed variant alone, which keeps
`π_is` — Figure 9's caption boxes only the user proof `π_iu` as removable.
(ii) Reading Theorem 5.3 as a statement about a `π_is`-less scheme outright,
dropping `π_is` from the variant.

**Fidelity argument.** The Theorem 5.11 proof answers its Sign queries with
the bare `(U′, V′)` and its bound carries no zero-knowledge term, so the
scheme the printed proof analyzes is the `π_is`-less core: a reduction
holding no secret key cannot produce real `π_is` proofs, and a
`π_is`-carrying scheme forces a simulation hybrid — hence a `zk_cmz.is`
term — into any correct bound. That rules out (i) as the object of the
printed proof. Removing `π_is` from the theorem instead is not viable
because the anonymity clause needs it (the user verifies `π_is`, protecting
against a key-substituting issuer; the anonymity simulator checks and
extracts it), ruling out (ii). The proposed erratum keeps `π_is` in the
scheme and adds one zero-knowledge term to the OMUF bound, obtained from the
core via the lifting lemma. Recorded as item 7 of
`docs/presentations/rolf-status/errata.md` and reported to the author.

#### 8. Figure 9 writes ℤ<sub>p</sub> where §5.1 and correctness need ℤ<sub>p</sub><sup>×</sup> (pp. 33–34)

*Status.* on `main`. *Kind.* impl.

**Where.** Figure 9 (p. 34) draws three scalars from ℤ<sub>p</sub>. They are
the server's issuance nonce u (U′ := uG), the user's issuance rerandomizer r
(U := rU′) and the user's presentation rerandomizer r ((U′, V′) := (rU, rV)).
The prose of §5.1 (p. 33) states the rerandomization property for r ≠ 0 and
draws the presentation rerandomizer from ℤ<sub>p</sub><sup>×</sup>.

**Why it is a problem.** The figure and the prose disagree, and only the
nonzero draws give a working run. A zero draw produces an honest value that a
check of the scheme then rejects, even when every proof verifies.

| Draw | Effect of a zero draw |
| --- | --- |
| Issuance nonce u | U′ = 0, rejected by the user's check U′ ≠ 0G |
| Issuance rerandomizer r | The credential (0, 0), rejected at presentation |
| Presentation rerandomizer r | U′ = 0, rejected by the server's check U′ ≠ 0G |

As printed, Figure 9 is therefore not perfectly correct. With perfectly
complete proofs an honest run fails with probability 1 − (1 − 1/p)<sup>3</sup>,
or 2/p − 1/p<sup>2</sup> for issuance alone. The error is negligible, so the
figure still satisfies Definition 4.3, and the inconsistency, not the error, is
the erratum. Drawing from ℤ<sub>p</sub><sup>×</sup> costs nothing and gives
perfect correctness. The base MAC has the same mismatch, with U ←$ 𝔾 in
Figure 9 and U ←$ 𝔾<sup>×</sup> in Eq. (1).

**How the formalization fixes it.** The formalization draws all three from
ℤ<sub>p</sub><sup>×</sup> with `uniformUnits`, the issuance nonces in PR #146
and PR #147 and the presentation rerandomizer in PR #206. No zero draw remains,
so the honest run never fails, and `μCMZCredential_correctRO` proves
correctness with probability one (PR #221).

**Formalization decision, from the design record, *Nonzero issuance nonces `u, r ←$ ℤ_p^×` where Figure 9 prints `ℤ_p`*.**

**Decision.** Both μCMZ_AT issuance nonces — the server nonce `u` and the
user re-randomizer `r` — are sampled from the nonzero scalars `F ∖ {0}` via
`uniformUnits` (`ATVariant.lean`; the sampler lives beside `uniformNonzero`
in `Construction.lean`).

**Rejected alternative.** Figure 9's literal `u ←$ ℤ_p` and `r ←$ ℤ_p`.

**Fidelity argument.** The two nonces have different justifications. For
`u`, the nonzero draw is the perfect-correctness convention, exactly as for the
base MAC's tag base (Eq. (1) samples `U ←$ 𝔾^×` while the figure writes the
looser `U ←$ 𝔾`): with `u = 0` the honest run aborts at the user's
`U′ ≠ 0` check, a `1/p` correctness-failure mass the support-based
`Correct` cannot account for. For `r`, the figure appears to be in error rather
than loose: §5.1 states the re-randomization property "for r ≠ 0", the
presentation step samples the same operation with `r ←$ ℤ_p^×`, and an
honest run with `r = 0` would emit the token `(0, 0)`, which the scheme's
own verifier rejects. Under the literal samplers honest issuance fails with
probability `2/p − 1/p²`. Reductions replaying issuance must account for
the per-nonce `1/p` distribution differences, as the AGM track already does for
the tag base (*Conditioned sign masks* above).

#### 13. Figure 9 samples H ←$ 𝔾, but §2.1.1 presents G and H as generators (pp. 11, 34)

*Status.* on `main`. *Kind.* impl.

Figure 9's setup draws H ←$ 𝔾, so H = 0<sub>𝔾</sub> with probability 1/p,
while §2.1.1 (p. 11) introduces "generators G and H". Definition 4.4 (p. 30)
quantifies over every crs ∈ [KVAC.S(1<sup>λ</sup>, n)], and at H = 0<sub>𝔾</sub>
the presentation's C<sub>V</sub> := V′ + r′H collapses to V′ = s·U′, so a
distinguisher holding sk wins with advantage above 1 − 4/p against every
simulator: anonymity under Definition 4.4 fails and Theorem 5.8 is false as
stated (corrected Example 1 on #149). The formalization draws H from
𝔾<sup>×</sup> (`uniformNonzero` in `setup`, `Schemes/MicroCMZ/Construction.lean`;
*Nonzero crs H ←$ 𝔾^×* in `docs/DESIGN_ALTERNATIVES.md`).

**Formalization decision, from the design record, *Nonzero crs `H ←$ 𝔾^×` where Figure 9 prints `𝔾`*.**

**Decision.** `μCMZ.setup` samples the crs element `H` from the nonzero
group elements `G ∖ {0}` via `uniformNonzero` (`Construction.lean`, issue
#149). The crs type stays the plain `G`; `H ≠ 0` is recovered where a proof
needs it from `mem_support_uniformNonzero`.

**Rejected alternative.** Figure 9's literal `H ←$ 𝔾`, under which `H = 0_𝔾`
with probability `1/p`.

**Fidelity argument.** Unlike the nonzero nonces above, this is not a
correctness convention: with `H = 0_𝔾` admissible, Definition 4.4 is false
for μCMZ, and no choice of simulator repairs it.

Indeed, Definition 4.4 (p. 30) quantifies over every
`crs ∈ [KVAC.S(1^λ, n)]`, each taken as a parameter, so one admissible crs
with non-negligible advantage refutes it. At `H = 0_𝔾` the presentation's
`C_V := V′ + r′H` collapses to `C_V = V′ = s·U′`, and a distinguisher with
advantage above `1 − 4/p` exists against every simulator; see the corrected
Example 1 on issue #149 for the full analysis.

Drawing `H` from `𝔾^×` removes `H = 0_𝔾` from the support of `setup`. The
other properties are unaffected; the OMUF bound of Theorem 5.11 loosens by
`(q + 3)/(p(p − 1))` (same analysis).

#### 14. Sim.P samples U′ ←$ 𝔾, but H5 needs U′ ≠ 0<sub>𝔾</sub> (pp. 40–41)

*Status.* on `main`. *Kind.* proof.

Sim.P (p. 40) "samples random group elements U′, C<sub>V</sub> ←$ 𝔾<sup>2</sup>",
and H5 (p. 41) argues U′ is "perfectly indistinguishable from the real one,
since r is uniformly distributed and U ≠ 0<sub>𝔾</sub>". With
r ←$ ℤ<sub>p</sub><sup>×</sup> (§5.1, *Credential presentation*, p. 33) and
U ≠ 0<sub>𝔾</sub> (item 8) the real U′ = rU is uniform on 𝔾<sup>×</sup>, while
the simulated U′ is 0<sub>𝔾</sub> with probability 1/p: statistical distance
1/p. Sampling U′ ←$ 𝔾<sup>×</sup> in Sim.P makes the two agree exactly.
Recorded on #149 (action 2). The simulator `μCMZAnonSimulator`
(`Schemes/MicroCMZ/Anonymity.lean`) samples u′ ←$ ℤ<sub>p</sub><sup>×</sup>
and sets U′ := u′G.

#### 15. Sim.P's Z omits the x<sub>r</sub>U′ term (pp. 34, 40–41)

*Status.* on `main`. *Kind.* proof.

Sim.P and H5 compute "Z = x₀U′ + Σᵢ γᵢXᵢ − C<sub>V</sub>" (pp. 40–41), while
Figure 9's server (p. 34) computes
Z = (x₀ + x<sub>r</sub>)U′ + Σᵢ xᵢCᵢ − C<sub>V</sub>; the two differ by
x<sub>r</sub>U′, so H5's "exactly the same in both distributions" fails.
Sim.P(st<sub>Sim</sub>, φ) holds neither x<sub>r</sub> nor m (Definition 4.4;
st<sub>Sim</sub> = (x₀, X₁, …, X<sub>n</sub>), p. 40), but with
t ←$ ℤ<sub>p</sub><sup>×</sup> and U′ := tG it can add
tX<sub>r</sub> = x<sub>r</sub>U′: then
Z = x₀U′ + tX<sub>r</sub> + Σᵢ γᵢXᵢ − C<sub>V</sub> equals the server's, and U′
is uniform on 𝔾<sup>×</sup> as item 14 requires. Recorded on #149 (action 3).
The simulator `μCMZAnonSimulator` adds u′X<sub>r</sub> to Z.

#### P22. Figure 9 samples U ←$ 𝔾, against Definition 3.1's correctness (pp. 25, 34)

*Status.* proposed on #217, awaiting review. *Kind.* impl.

µCMZ.M draws U ←$ 𝔾 while µCMZ.V rejects U = 0<sub>𝔾</sub>, so an honestly
generated MAC fails to verify with probability 1/p, against Definition 3.1's
requirement that "every honestly generated MAC verifies" (p. 25). Lemma 5.4's
proof asserts "Statistical correctness follows by inspection" (p. 36); a 1/p
failure is consistent with statistical correctness but not with the
definition. Eq. (1) (p. 11) draws U ←$ 𝔾<sup>×</sup> for CMZ; Claim 5.6's
simulated Sign follows Figure 9 (u ←$ ℤ<sub>p</sub>). Item 8 notes the mismatch
in passing. The formalization draws U from 𝔾<sup>×</sup> (`uniformNonzero` in
`mac`, `Construction.lean`). Documented in
`docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`, section "Sampling of U".

**Formalization decision, proposed on #217 with the item, *Nonzero tag base U ←$ 𝔾^× in the base MAC, where Figure 9 prints 𝔾*.**

**Decision.** μCMZ.M samples the tag base U from the nonzero group elements G ∖ {0}, via uniformNonzero (mac, Construction.lean). The tag type stays G × G; a proof that needs U ≠ 0 obtains it from mem_support_uniformNonzero. The simulator of Claim 5.6 samples its signing scalar from ℤ_p^× for the same reason (gapSignScalarSample := uniformUnits F, AGMReduction/GapDLReduction.lean).

**Rejected alternative.** Figure 9's U ←$ 𝔾 in µCMZ.M (p. 34), under which U = 0_𝔾 with probability 1/p.

**Fidelity argument.** The paper gives two samplers for U, and only one of them satisfies its own correctness definition.

Eq. (1) (p. 11) defines the CMZ MAC with U ←$ 𝔾^×.
Figure 9's M writes U ←$ 𝔾, while its V rejects U = 0_𝔾. Under this sampler an honestly generated tag fails to verify with probability 1/p.

Definition 3.1 (p. 25) requires that "every honestly generated MAC verifies". The repository's Correct predicate (KVAC.Core.AlgebraicMAC.Correctness) formalises this requirement as: every tag in the support of M verifies. Under Figure 9's sampler the predicate is false; under Eq. (1)'s it is proved (μCMZBaseMAC_correct).
The proof of Lemma 5.4 states only that "Statistical correctness follows by inspection" (p. 36). Statistical correctness admits a 1/p failure; Definition 3.1 does not.

Reductions that simulate Sign must match the real U, uniform on 𝔾^×: Lemma 5.4's conditions its sign masks on U_j ≠ 0 (entry Conditioned sign masks, earlier in this file); Claim 5.6's draws its scalar u from ℤ_p^× (gapSignScalarSample, AGMReduction/GapDLReduction.lean). Both are in place; neither changes a bound.

### A4. The overview statements disagree with the proved theorems

#### 17. Theorem 1 prints Adv<sup>simex</sup> where Theorem 5.8 prints Adv<sup>ksnd</sup> (pp. 4, 40, 42)

*Status.* on `main`. *Kind.* proof.

The anonymity advantage of Theorem 1 (p. 4) is
2Adv<sup>zk</sup><sub>ZKP</sub> + Adv<sup>simex</sup><sub>ZKP</sub>, while
Theorem 5.8 (p. 40) bounds it by
Adv<sup>zk</sup><sub>ZKP<sub>cmz.iu</sub></sub> +
Adv<sup>zk</sup><sub>ZKP<sub>cmz.p</sub></sub> +
Adv<sup>ksnd</sup><sub>ZKP<sub>cmz.is</sub></sub>. The two differ in the
extraction term, simulation extractability in the overview and knowledge
soundness in the theorem. Hybrid H3 (p. 41) extracts from a π<sub>is</sub>
the issuer produced after the simulated π<sub>iu</sub> of H1, which the
knowledge-soundness game of §3.3 does not cover. Remark 5.9 states the mirror
case, π<sub>iu</sub> after simulated π<sub>is</sub>, the direction of
Theorem 5.10. Remark 5.9
(p. 42) says that knowledge soundness suffices for Schnorr proofs because
"the vector sizes mismatch", without a proof. Theorem 5.8 is printed for any
"proof system for the relation R ⊇ R<sub>cmz</sub>", while the Remark's
justification covers Schnorr proofs alone. No prose connects Theorem 1 and
Remark 5.9. The formalization keeps the printed Theorem 5.8 and states the
Remark as the lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated` in
`Core/NIZKP/Composition.lean`, with the mismatch as an explicit region of the
random-oracle domain.

**Formalization decision, from the design record, *Theorem 5.8 with the printed knowledge-soundness term*.**

**Decision.** The bound of `μCMZ_anonymity` (`Schemes/MicroCMZ/Anonymity.lean`)
carries `KSNDAdv` of `ZKP_cmz.is` as Theorem 5.8 prints it. The theorem takes
as hypotheses the condition of Remark 5.9 in four forms of
`Core/NIZKP/Composition.lean`. `ConfinedSystem` confines the setup, prover and
verifier of each of the three proof systems to a region of the random-oracle
domain, `ZKSimulatorConfinedTo` confines the simulators of `ZKP_cmz.iu` and
`ZKP_cmz.p` to the region of their system, `TraceExtractor.ConfinedTo`
confines the extractor of `ZKP_cmz.is` to the region of its system, and
`Region.Disjoint` makes the three regions pairwise disjoint. The property
hybrid H3 uses is `KSNDSimAdv`, knowledge soundness in the presence of
simulated proofs of `ZKP_cmz.iu`. The lemma
`ksndSimAdv_le_ksndAdv_of_domainSeparated` bounds it by the printed term. The
zero-knowledge step H2 needs the condition as much as H3. Its reduction runs
the simulator of `ZKP_cmz.iu` inside the zero-knowledge game of `ZKP_cmz.p`,
which offers the random oracle only, while Remark 5.9 raises the point for
extraction alone. The Remark states its case for `π_iu` after simulated
`π_is`, the direction of Theorem 5.10, and H3 of Theorem 5.8 is the mirror
case, which the lemma covers as well.

**Rejected alternative.** Replacing the knowledge-soundness term by a
simulation-extractability term `SEAdv`, as Theorem 1 (§1, p. 4) prints
`Adv^simex` where Theorem 5.8 prints `Adv^ksnd`, or stating the bound with
`KSNDSimAdv` directly.

**Fidelity argument.** The bound of Theorem 5.8 is the one to formalize, and
Remark 5.9 is the paper's own argument that knowledge soundness suffices for
the Figure 9 proof systems. Theorem 5.8 (p. 40) is printed for any "proof
system for the relation R ⊇ R_cmz", while the Remark gives its argument for
Schnorr proofs alone, without a proof. The formal theorem states what the
printed proof proves and takes the condition as hypotheses, since no proof of
the printed form exists. The formalization states the Remark as a lemma over any
proof system, with an explicit region of the random-oracle domain in place of
"the vector sizes mismatch". `DomainSeparated` is the Remark's "different
random oracles" within one oracle, the mechanism the Remark names, and is
wider than the Schnorr instance. The Remark's own requirement, that the
simulated proofs "cannot be turned into proofs" of the other relation, has no
formal counterpart. The instance fact for the compiled Σ-protocols waits
for issue #3, and until then no call site discharges the hypotheses. Errata
item 17 records the difference between Theorem 1 and Theorem 5.8.

#### 18. Theorem 5.3 charges Adv<sup>zk</sup><sub>cmz.iu</sub> to a scheme without π<sub>iu</sub> (pp. 35, 40–41)

*Status.* on the branch `microcmz-theorem-5-3` (#184). *Kind.* proof.

Theorem 5.3 (p. 35) bounds the anonymity advantage of μCMZ<sub>AT</sub> by
Adv<sup>zk</sup><sub>ZKP<sub>cmz.iu</sub></sub> +
Adv<sup>zk</sup><sub>ZKP<sub>cmz.p</sub></sub> +
Adv<sup>ksnd</sup><sub>ZKP<sub>cmz.is</sub></sub>, the bound of Theorem 5.8
(p. 40) unchanged, "from the above". μCMZ<sub>AT</sub> is defined on p. 35 as
Figure 9 "where the issuance algorithm does not return the proof
π<sub>iu</sub>". The first term pays for hybrid H1 of the Theorem 5.8 proof
(p. 41), which replaces the user's π<sub>iu</sub> by a simulated one. The
token's user sends no π<sub>iu</sub>, so H1 changes nothing and the term is
vacuous. The hypothesis of Theorem 5.3 agrees, since its relation
R ⊇ R<sub>cmz.p</sub> ∪ R<sub>cmz.is</sub> names no R<sub>cmz.iu</sub>.

Proposed correction: the anonymity bound of Theorem 5.3 is
Adv<sup>zk</sup><sub>ZKP<sub>cmz.p</sub></sub> +
Adv<sup>ksnd</sup><sub>ZKP<sub>cmz.is</sub></sub>. The formalization states
the clause with the two terms, in the Theorem 5.3 statement under issue #184,
and the simulator of that statement is the Theorem 5.8 simulator without its
π<sub>iu</sub> simulator.

#### 19. Theorem 5.3 prints the one-more unforgeability bound of the October 2024 version (pp. 35, 43)

*Status.* on the branch `microcmz-theorem-5-3` (#184). *Kind.* proof.

Theorem 5.3 (p. 35) bounds the one-more unforgeability advantage of
μCMZ<sub>AT</sub> by
Adv<sup>2dl</sup> + q·Adv<sup>dl</sup> + (q+5)/p, "from the above, and
Theorem 5.11". Theorem 5.11 (p. 43) prints
(q+6)/p + (q+1)·Adv<sup>dl</sup> + 3·Adv<sup>2dl</sup> + Adv<sup>gapdl</sup>,
the sum of Claims 5.12 to 5.14 (Equation 23, p. 46) and of the general-n
case, so Theorem 5.11 does not imply the printed Theorem 5.3. The ePrint
history explains the gap. In the version of 3 October 2024 the §5 theorem
(then Theorem 14) printed
2·Adv<sup>2dl</sup> + q·Adv<sup>dl</sup> + (q+5)/p, with one discrete-log
reduction credited to [CDV22], and the summary theorem (then Theorem 9)
printed the bound above, already off by one in the 2-DL coefficient. The
revision of 24 February 2025 rewrote the proof into the three Claims and
changed the bound of Theorem 5.11, and Theorem 5.3 was not updated. Theorem 1
(p. 4), present from the version of 27 March 2026 on, follows the revised
Theorem 5.11 with O(q)·Adv<sup>dl</sup> + 3·Adv<sup>2dl</sup>. No version
proves the bound printed in Theorem 5.3.

Proposed correction: the one-more unforgeability bound of Theorem 5.3 is that
of Theorem 5.11, plus the Adv<sup>zk</sup><sub>cmz.is</sub> term of item 7.
The formalization states the clause with `omufBound` of
`Schemes/MicroCMZ/OneMoreUnforgeability/Statements.lean` and that term, in
the Theorem 5.3 statement under issue #184.

### A5. Proof steps missing or misdirected as printed

#### P16. Claim 5.6's simulated Verify omits the U ≠ 0<sub>𝔾</sub> check (p. 39)

*Status.* proposed on #217, awaiting review. *Kind.* proof.

Figure 9's verifier (p. 34) accepts iff U ≠ 0<sub>𝔾</sub> and the equation
holds; the simulated Verify of Claim 5.6 tests only the verification equation
(directly when Σᵢ bᵢmᵢ = 0, through Ddh otherwise). On Verify(m, (0<sub>𝔾</sub>,
0<sub>𝔾</sub>)) the printed simulation answers 1 for every m — both branches
hold trivially at U = V = 0 — while the real oracle answers 0, so the
simulation is not perfect as printed. Restoring the conjunct costs nothing; the
formalization checks it (`gapDlOracleImpl`, `AGMReduction/GapDLReduction.lean`).
Documented in `docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`, Lemma 5.6.1 and
the Remark "Claim 5.6's Verify formula is wrong as printed".

#### P18. Claim 5.7 forwards messages but not algebraic representations (pp. 39–40)

*Status.* proposed on #217, awaiting review. *Kind.* proof.

The n → 1 reduction plays the 1-attribute AGM game, so the Verify and Help
queries it relays, and its forgery, need representations over the 1-attribute
basis (G, H, X₀, X<sub>r</sub>, X₁, U<sub>j</sub>, V<sub>j</sub>). The paper
forwards Sign and Verify queries with the message collapsed to
m₁ + Σᵢ₌₂ⁿ zᵢmᵢ, treats Help "similarly", and never mentions representations,
although A's are over the n-attribute basis, whose X₂, …, X<sub>n</sub> the
challenger has never seen. The missing step folds α₂, …, α<sub>n</sub> into
the X₁ coordinate, α₁ + Σᵢ₌₂ⁿ zᵢαᵢ, at Verify, Help and the forgery. Recorded
in `docs/DESIGN_ALTERNATIVES.md` ("Claim 5.7: the n → 1 collapse translates
representations, not only messages"); defined, without theorems yet, in
`AGMReduction/AttributeCollapse.lean` (`AGMRepr.collapseRepr`,
`AGMRepr.linCombCollapse`). Documented in
`docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md` as τ and Lemma 5.7.2.

#### S1. Eq. 14 gives the Verify arm two powers where the degree needs three (p. 37)

*Status.* proposed in Semar's report of 28 October, not yet on #217. *Kind.* proof.

Eq. 14 (p. 37) gives the Verify oracle of the reduction only the powers (X, X′) of the 3-DL instance, "as the maximum degree of the resulting polynomial is 2". The represented verification check is the product of the key polynomial, of degree 1 (`totalDegree_keyPoly_le`), and the representation polynomial, of degree at most 2 (`totalDegree_toPoly_le`, reached by the monomials x₀η and uⱼ(x₀ + xᵣ + mⱼx₁)), so it has degree at most 3 and not 2, and the Verify arm evaluates against (G, X, X′, X″) as the Help arm does (`exponentEval`, `AGMReduction/Core.lean`). Recorded so far in the design record alone, under *Eq. 14: the simulated signing response*, whose second correction this is; item 4 records the coefficient.

#### S2. Lemmas 5.4 and 5.5 send Help to Theorem 5.11, whose proof never uses it (pp. 36, 38, 42–43)

*Status.* proposed in Semar's report of 28 October, not yet on #217. *Kind.* proof.

The proofs of Lemmas 5.4 and 5.5 say that giving the adversary the oracle Help "will simplify the proof of Theorem 5.11" (pp. 36, 38). The proof that uses Help's answer is Theorem 5.10's, extractability: p. 42 assumes the candidate Z can be checked through Help, and p. 43 uses Help's answer for the first equality of its display. The proof of Theorem 5.11 (pp. 43 to 47) never mentions Help. Raised in Semar's review of PR #243 and recorded in the design record under *Theorem 5.10 at the honest UF-CMVA game with Help*.

## Part B. Decisions where the paper leaves something implicit

These are not errors. The paper says less than a machine needs, and the
formalization chose. Each entry keeps the form of the design record, the
decision, the rejected alternative and the fidelity argument, and where the
decision landed. The entries that answer an erratum are under their item in
Part A: *Schwartz–Zippel bound 3/p* under item 1, *Eq. 13* under item 3,
*Eq. 14* under item 4, *The μCMZ_AT core* under item 7, *Nonzero issuance
nonces* under item 8, *Nonzero crs H* under item 13, *Theorem 5.8 with the
printed knowledge-soundness term* under item 17, and *Nonzero tag base U* under
item P22.

### B1. The proof-system layer (O24 §3.3)

How the generic NIZKP object, its games and its extractor are stated.

#### Security-model-agnostic specification set aside

**Decision.** The paper-level NIZKP object is the game-based O24 §3.3
specification (`Construction.lean`, `Completeness.lean`, `Security.lean`;
PRs #45, #46, #47). The security-model-agnostic specification (`Basic.lean`,
the `SecurityModel` typeclass; PR #26) stays in the tree, and the root no
longer imports it (da1dcf5).

**Rejected alternative.** Building the μCMZ/μBBS security proofs directly over
the agnostic specification, which states `KnowledgeSound`, `ZeroKnowledge`,
and `SimulationExtractable` over an abstract carrier `F` with model-supplied
relations `indist`, `produces`, and `extracts` (PRs #28, #29, #34, closed
unmerged).

**Fidelity argument.** O24 §3.3 defines the notions computationally, by games
with advantage negligible in λ. The agnostic relations abstract exactly that
content away, so a §3.3 citation over `Basic.lean` covers the shape of the
property but not its security content. The abstraction is set aside, not
discarded; issue #43 tracks its revisit.

#### Extractor and simulator exhibited existentially

**Decision.** The knowledge-soundness extractor and the zero-knowledge
simulator are exhibited in the security statements, not fields of the scheme
or of a security model (PR #34 introduced this; the paper-faithful
specification keeps it).

**Rejected alternative.** Extraction as a `SecurityModel` attribute
(`SecurityModel.extracts`) read by the properties.

**Fidelity argument.** In O24 §3.3 and in the standard definitions the
extractor is external to the game and to the scheme description. Tom Shrimpton
raised the point; issue #43 records it as resolved.

#### Monadic verifier

**Decision.** `NIZKPSyntax.verify` returns `M Bool` (PR #45,
`Construction.lean`).

**Rejected alternative.** A deterministic verifier returning `Bool`, like
`MAC.V` of O24 §3.2.

**Fidelity argument.** O24 writes 0/1 ← ZKP.V with a sampling arrow, unlike
the deterministic 0/1 := MAC.V of §3.2, and a Fiat–Shamir verifier recomputes
c = H(a, x) through the random oracle, so the verifier must be effectful.

#### Proveᵦ guard, oracle-side check with an `Option` answer

**Decision.** The Proveᵦ oracle of the zero-knowledge game answers
`Option (Proof crs)`. `zkProveReal` and `zkProveSim` check (x, w) ∈ R through
`NIZKPSyntax.DecidableRelation` and answer `none` on a non-witnessed query,
identically in both worlds (PR #47, commit 5829842).

**Rejected alternative.** A type-level guard where `ZKQuery.prove` carries a
proof of `relation crs x w`, so the adversary can only submit witnessed pairs.
It avoids the `Option` answer type and the decidability argument, and it is
equivalent in adversarial power, since rejected queries answer identically in
both worlds and carry no information.

**Fidelity argument.** O24 §3.3 defines Proveᵦ(x, w) as an oracle that "checks
if (x, w) ∈ R" before answering. The check belongs to the oracle, not to the
query interface, and a type-level restriction silently narrows the game's
interface. The `none` answer encodes the paper's implicit ⊥.

#### Relation decidability scoped to the game

**Decision.** `Decidable (relation crs x w)` is required only by the
zero-knowledge game that runs the Proveᵦ guard, supplied as a game argument
through `NIZKPSyntax.DecidableRelation`. `NIZKPSyntax.relation` stays a plain
`Prop`-valued field with no decidability (PR #47, `Security.lean`).

**Rejected alternative.** Making decidability intrinsic to the syntax, a
`DecidableRel` field or instance on `NIZKPSyntax.relation`, so every scheme
value carries a decision procedure.

**Design argument.** A `Decidable` instance is data, a computable decision
procedure, not a derivable property. `NIZKPSyntax.relation` is an abstract
field, so over a generic scheme it is an arbitrary `Prop`-valued function with
no decision procedure available; closing it classically is noncomputable and
the `ProbComp` guard would not execute. A concrete scheme supplies both the
relation and its decision procedure. The game that runs the guard is the only
consumer that needs the procedure, so scoping the obligation there keeps a
generic `NIZKPSyntax` from carrying a procedure it cannot provide, while
concrete schemes over decidable-equality carriers supply it directly. The
choice does not rest on decidability failing, since the NP relations O24's
proof systems target are always decidable, and it differs from the extractor,
which is externalized because it varies per protocol rather than because it is
data unavailable over a generic scheme.

The monad polymorphism of `NIZKPSyntax` realizes the computational layer on
VCV-io's `ProbComp`, which is a free monad on a polynomial functor
(`PFunctor.FreeM`). That realization touches only the `M`-valued operations
`setup`, `prove`, and `verify`; `relation` stays `Prop`-valued and outside
`M`. Decidability is therefore orthogonal to the monad choice and scoped to
the game rather than the carrier.

#### White-box knowledge-soundness extractor

**Decision.** The knowledge-soundness and simulation-extractability extractors
are white-box, per O24 §3.3 (p. 25), which has Ext take "the random coins and
the code of the p.p.t. adversary A". The extractor receives the adversary
value (the code) and the run's observables, that is, the output pair, the final
random-oracle cache, and, for simulation extractability, the simulation log. The
adversary's coins are not recorded. The optional crs trapdoor is omitted, the
paper's instantiations never use it (PR #54, `Extraction.lean`).

**Rejected alternative.** The standard black-box convention, where the
extractor has rewindable oracle access to the prover and sees neither its
coins nor its code. Tom Shrimpton advocated it during the review of the
security-model-agnostic specification (PR #34), before the paper-faithful
specification existed; it is not a comment on the extraction layer now
committed.

**Fidelity argument.** O24 defines the extractor over the coins and code of A,
and its §9 instantiation is inherently non-black-box, since it relies on AGM
representations. The formalization gives the extractor the adversary value
together with the run's observables, the output pair and the final random-oracle
cache, and the simulation log for SE. The coins themselves are not recorded, so
same-coins replay and rewinding are out of scope, unneeded by the straight-line
§9 instantiation. Issue #43 records the discussion; the paper-fidelity
requirement decides it.

**Open question, the AGM extractor interface.** Whether the extractor needs an
ordered `QueryLog` alongside the cache, or a `QuerySeed` for the literal coins,
is left to the AGM extractor design of §9. VCV-io ships both, `loggingOracle`
and `seededOracle`. Deciding before an extractor consumes this layer avoids
restating the games later.

#### NIZKP procedure carrier and the `verify` effect

**Decision.** Instantiate the generic `NIZKPSyntax M` of `Construction.lean` at
`M = OracleComp (ZKRO H)`, so `setup`, `prove`, and `verify` share one carrier
and every honest algorithm may read the random oracle `H`. In particular
`verify : … → OracleComp (ZKRO H) Bool`, which a Fiat–Shamir verifier needs to
recompute its challenge `c = H(R, x)` from the same oracle the proof was built
against. This keeps the generic structure unchanged and threads one cache
through the adversary and `verify` in the games.

The single thing this carrier does not pin is that `verify` draws no coins of
its own. Since `ZKRO H = unifSpec + H.spec`, the type still exposes the sampling
arm, so a verifier that sampled fresh randomness would type-check. That
guarantee is deferred to a lemma added when the concrete Fiat–Shamir scheme of
§5 lands, consumed by the §9 straight-line extraction (issue #101).

**Bespoke alternatives.** Each moves the no-sampling guarantee into the type of
`verify`. Each edits the structure, so each is bespoke and diverges from the
generic single-monad `NIZKPSyntax M`. In both, `unifSpec` is unreachable from
`verify`, so a coin-sampling verifier is not expressible.

Alternative A, `verify` fixed to the narrower hash-only monad. Every algorithm
gets its narrowest effect.

```lean
structure NIZKPSyntaxFixed (H : HashSpec) where
  Crs     : Nat → Type
  Stmt    : {secParam : Nat} → Crs secParam → Type
  Witness : {secParam : Nat} → Crs secParam → Type
  Proof   : {secParam : Nat} → Crs secParam → Type
  setup   : (secParam : Nat) → ProbComp (Crs secParam)
  prove   : {secParam : Nat} → (crs : Crs secParam) →
              Stmt crs → Witness crs → OracleComp (ZKRO H) (Proof crs)
  verify  : {secParam : Nat} → (crs : Crs secParam) →
              Stmt crs → Proof crs → OracleComp H.spec Bool
  relation : {secParam : Nat} → (crs : Crs secParam) →
              Stmt crs → Witness crs → Prop
```

Alternative B, `verify` polymorphic over a hash-only capability. No second
concrete monad is committed, and `verify` may bind, return, and hash, nothing
else.

```lean
/-- A monad exposing exactly the `H` random oracle and no other effect. -/
class HashOnly (H : HashSpec) (N : Type → Type) [Monad N] where
  hash : H.Dom → N H.Rng

structure NIZKPSyntaxCap (H : HashSpec) where
  Crs     : Nat → Type
  Stmt    : {secParam : Nat} → Crs secParam → Type
  Witness : {secParam : Nat} → Crs secParam → Type
  Proof   : {secParam : Nat} → Crs secParam → Type
  setup   : (secParam : Nat) → ProbComp (Crs secParam)
  prove   : {secParam : Nat} → (crs : Crs secParam) →
              Stmt crs → Witness crs → OracleComp (ZKRO H) (Proof crs)
  verify  : {secParam : Nat} → (crs : Crs secParam) → Stmt crs → Proof crs →
              {N : Type → Type} → [Monad N] → [HashOnly H N] → N Bool
  relation : {secParam : Nat} → (crs : Crs secParam) →
              Stmt crs → Witness crs → Prop
```

**Why deferred rather than adopted.** Both alternatives pay at every use site.
Alternative A lifts `verify` from `H.spec` into `ZKRO H` in each game and in the
completeness statement. Alternative B carries a monad-polymorphic field and
instantiates `N` with its `HashOnly` instance everywhere `verify` runs. Both
replace the generic `NIZKPSyntax M` the rest of the layer speaks with an
H-indexed record. With the chosen carrier the same Fiat–Shamir faithfulness
holds with the generic structure untouched, and the no-sampling guarantee is
recoverable later as a lemma that `verify` factors through `H.spec`, which is
precisely Alternative A's type read back as a property, without committing the
structure now.

#### Structured hash domains

**Decision.** `HashSpec.Dom` is an arbitrary type; each scheme picks a
structured domain type for what it hashes (PR #57, `Core/Hash.lean`).

**Rejected alternative.** Fixing `Dom := List Bool` to match the paper's
`{0,1}*` literally.

**Fidelity argument.** A typed-domain random oracle is a *stronger* model
than the paper's: distinct Lean values answer independently, where their
bitstring serializations could collide. The divergence is deliberate and
documented in `Core/Hash.lean`: a concrete instantiation owes an injective
canonical encoding of its domain type and domain-separation tags wherever
two uses share one oracle. A literal bitstring domain would push encoding
boilerplate into every caller without strengthening any theorem.

### B2. The framework (O24 §4)

Predicates, correctness, the anonymity game of Definition 4.4 and the extractability game of Definition 4.5.

#### Exact-attribute predicate as a family field

**Decision.** `PredicateFamily` carries the full-disclosure predicate
`exactPred` (`φ_m⃗`) with its semantic law `holds_exactPred`
(`Framework/PredicateFamily.lean`).

**Rejected alternative.** Parameterizing the security games by an arbitrary
selector `(m⃗ : MsgVec crs) → Pred crs`, leaving the family at the literal
Definition 4.1 content (trivial predicate, conjunction).

**Fidelity argument.** O24 Definition 4.2 requires the predicate family to
contain the partial-disclosure predicates `{φ_a⃗ : a⃗ ∈ (M ∪ {⋆})ⁿ}`, and the
framework's own games consume exactly one member of that set: Figure 8's
`NewUsr` runs the §4.1 shorthand `KVAC.M(sk, m⃗) = issue(…, φ_m⃗)`. A game
parameter would let a scheme instantiate the games with a non-exact predicate,
silently changing what the security notions mean; a field with a semantic law
is checked once per scheme. The rest of the partial-disclosure family stays a
scheme-level obligation (the TODO recorded in `Framework/Correctness.lean`).

#### Correctness requires issuance to succeed before presentation runs

**Decision.** `CorrectOutcome` (`Framework/Correctness.lean`) asks every
issuance outcome to be `some σ`, and only then asks every presentation bit
from that `σ` to be `true`. A failed issuance violates correctness on its own,
with no presentation bit. The types enforce the order, since `issueUsr₂`
returns `Option Cred` and `presentUsr` takes a `Cred`.

**Rejected alternative.** A presentation that also accepts `⊥`, with the
convention that the server rejects it, so that `σ = ⊥` yields `b = 0`. The
experiment would then compute a `Bool` on every run, at the cost of an
`Option Cred` input to `presentUsr` that no scheme uses.

**Fidelity argument.** The paper leaves this case implicit. O24 Definition 4.3
runs `σ ← (KVAC.I.Usr ⇌ KVAC.I.Srv)` and then
`b ← (KVAC.P.Srv ⇌ KVAC.P.Usr(pp, m⃗, σ, φ'))`. Issuance fails when the issuer
rejects the user's message and returns `σ' = ⊥` (O24 §4.1), or when a `check`
line of the user fails (Figure 9). The paper defines `KVAC.P.Usr` on credentials
only, so the experiment assigns no value to `b` after a failed issuance. Both
readings, `b = 0` on `⊥` and the success event `σ ≠ ⊥ ∧ b = 1`, give the same
probability. The decision states the second
reading, which needs no convention on `⊥`.

#### No obligation theorem for `ExtractablePoly`

**Decision.** `Framework/Extractability.lean` states the predicates `Extractable`,
`PolyBounded` and `ExtractablePoly` of O24 Definition 4.5 and no theorem about
them. The theorem `extractablePoly_obligation`, added by PR 126 as an
"obligation generator" asserting `ExtractablePoly H kvac isPPT` for every scheme
and every efficiency predicate with a `sorry`, is removed (issue #177, item 12 of
`docs/MICROCMZ_REMAINING.md`).

**Rejected alternatives.** Keeping the theorem with the premises its docstring
elided, scheme correctness and knowledge-sound proof systems, which an abstract
`kvac` cannot name. Specializing it to the μCMZ instance, which at a fixed group
is the asymptotic clause of Theorem 5.10 with no route to a proof (*The crs and
the group* below). A bridging lemma from a negligible bound to `ExtractablePoly`,
which is VCVio's `negligible_of_le` and belongs inside the proof of the asymptotic
clause, not to the framework.

**Fidelity argument.** The statement without premises is false. A scheme with
inhabited message types whose server presentation check accepts every
presentation, with the constantly true efficiency predicate, lets an adversary
that makes no oracle query and outputs any pair win `EXTGame` with probability
one for every extractor, since the honest-presentation and issued lists are
empty and only the accept bit counts. The paper has no such theorem. Theorem
5.10 (§5.5, p. 42) states "μCMZ is extractable for n = poly(λ) attributes with
advantage" followed by its inequality, and its proof (pp. 42 to 43) builds the
reductions without naming negligibility. The inequality is item 13, stated at
fixed parameters as Theorem 5.8 is. The clause "extractable" is `ExtractablePoly`
at the μCMZ instance under the negligibility of the four terms for the reduction
adversaries, which issue #148 carries. At the fixed group of the instance p
does not grow with λ, so 3/p is a positive constant and this bound cannot
establish negligibility. The paper's asymptotic argument requires a λ-indexed
group family.

#### Anonymity game at fixed setup, negligibility over instance families

**Decision.** The anonymity games `anonGameReal` and `anonGameSim`
(`Framework/Anonymity.lean`, PR #186) take the crs, the key pair, the attribute
vector, the predicate and the initial random-oracle table as parameters. The
predicate `Anonymous` quantifies over families of admissible instances indexed
by the security parameter, one `AnonInstance` per λ with the support
hypotheses, and asks the resulting function of λ to be negligible.

**Rejected alternative.** Sampling the crs and the keys inside the game and
letting the adversary choose the attribute vector and the predicate, as
`EXTGame` does for Definition 4.5 and as `zkRun` does for zero knowledge.

**Fidelity argument.** Definition 4.4 quantifies "for all crs ∈ [KVAC.S(1^λ, n)]
and (sk, pp) ∈ [KVAC.K(crs)], m⃗ ∈ M^n, φ ∈ Φ such that φ(m⃗) = 1" and then
asks for negligibility in λ. A game that samples setup bounds the average over
the crs, and an average does not bound the advantage at every crs, since a rare
crs may carry advantage one while contributing little to the mean. The
pointwise reading is the paper's. Its cost is that the zero-knowledge and
knowledge-soundness advantages of the repository are sampled, so the Theorem
5.8 statement must bridge the two formulations.

#### The issuer adversary runs before and after the user's request

**Decision.** `AnonIssuer` has two runs, `prepare` before the user speaks and
`respond` on the request μ, with a private state between them, both with
random-oracle access.

**Rejected alternative.** One run of A on μ, after the user's first move.

**Fidelity argument.** A(sk, pp, φ, m⃗) is an oracle algorithm in the random
oracle model and queries at any time. With one run after μ, an adversary
cannot compare an oracle value it saw earlier with the value a simulator
programmed at its first move, so a simulator that reprograms the oracle when
it forms the request is undetectable and the game is weaker than the paper's.
One round of issuance bounds the protocol messages, not the adversary's local
oracle computation.

#### Two adversary structures, not one pair

**Decision.** `AnonIssuer` and `AnonDistinguisher` are two structures. The
distinguisher takes the issuer's state type as a parameter, and the
efficiency predicate of `Anonymous` is on the two.

**Rejected alternative.** One record bundling A and D with a shared state type,
on the ground that D receives A's output.

**Fidelity argument.** Definition 4.4 names "adversaries A, D" and its variants
constrain them separately, statistical anonymity for unbounded A and D, and
everlasting forward anonymity for unbounded D alone. A shared record needs
one efficiency predicate on the pair and leaves the everlasting variant to
prose. Two structures make it a declaration,
`EverlastingForwardAnonymous`. The shared state type is a typing constraint
that a parameter carries as well as a record does.

#### The anonymity simulator runs in the random-oracle state monad

**Decision.** The three procedures of `AnonSimulator` have type
`StateT HS.spec.QueryCache ProbComp _`, as `ZKSimulator` does, so they read and
may reprogram the oracle table.

**Rejected alternative.** The carrier `OracleComp (ZKRO HS)` of the honest
algorithms, which queries the oracle and cannot program it.

**Fidelity argument.** O24 §3.3 grants a simulator the power to "explicitly
re-program the random oracle", and the §5.4 simulator of Theorem 5.8 calls the
proof systems' simulators to form π_iu and π_p. A simulator without that power
would define a stronger notion than the paper's, and Theorem 5.8 would not be
provable for it.

#### The Present oracle answers under the queried predicate

**Decision.** `anonPresentImpl` answers `Present_b(φ')` with
`KVAC.P.Usr(pp, m⃗, σ, φ')` or `Sim.P(st_Sim, φ')`, the predicate of the query.

**Rejected alternative.** The paper's oracle line as printed, which returns
`KVAC.P.Usr(pp, m⃗, σ, φ)` and `Sim.P(st_Sim, φ)` with the issuance predicate
`φ`.

**Fidelity argument.** The same line checks "if φ′(m⃗) holds", and a
presentation under φ regardless of φ′ would leave the oracle's argument idle
and let the distinguisher request only presentations of the issuance
predicate. The comparison with CMZ14 that follows the definition speaks of
presentations under the predicates the verifier asks for. The printed φ reads
as a typo for φ′.

#### The extractor of Definition 4.5 takes the random-oracle table

**Decision.** `Extractor` of `Framework/Extractability.lean` receives the
random-oracle table as of the call and runs in `ProbComp`. The `Issue` oracle
and the win condition of `EXTGame` pass it the table as of the call, before
the server's own computation, as `ksndGame` does. `μCMZExtractor` of the Theorem 5.10 statement (#179) wraps the trace extractors of `ZKP_cmz.iu` and `ZKP_cmz.p`, with `Ext.P` recomputing
`Z` from the secret key as the server does.

**Rejected alternative.** The pure extractor without the table of the first
version of the game, `Sk → Pred → IssueMsg → Option MsgVec`.

**Fidelity argument.** Figure 8 (p. 31) writes `m := Ext.I(sk, φ, μ)` and
`m* := Ext.P(sk, φ*, ρ*)`, and the proof of Theorem 5.10 (pp. 42 to 43)
defines both from the extractors of the proof systems, which read the trace
of random-oracle queries and are algorithms. A pure extractor without the
table cannot be instantiated by them. The secret key stays an argument, since
Figure 8 prints it and `Ext.P` uses it to compute `Z` (p. 43, "internally,
the extractor checks that Z was correctly computed via the secret key").

### B3. The MAC and its reductions (O24 §5.3)

The reductions of Lemmas 5.4 and 5.5 and the game of Theorem 5.1.

#### Conditioned sign masks

**Decision.** The reduction's sign masks are sampled conditioned on Uⱼ ≠ 0 
(`SignMask.lean`, PR #48), giving exact coupling with the real oracle.

**Rejected alternative.** The paper's unrestricted `a_{u,j}, b_{u,j} ←$ ℤ_p` (Eq. 14).

**Fidelity argument.** The real experiment's U is uniform over `𝔾^×` and never zero, 
so Eq. 14's "identically distributed" holds only under the conditioning. 
The `(Uⱼ, bᵤ)` joint law stays independent uniform (`sign_U_bu_dist_eq`), 
so the masks' hiding is unaffected.

#### Conditioned η masks

**Decision.** The 3-DL reduction's η masks `(aη, bη)` are sampled conditioned on
`H = aη·G + bη·X ≠ 0`, by the sign-mask sampler `reductionMaskSample`
(`AGMReduction/Core.lean`, `redTrace`).

**Rejected alternative.** The paper's unrestricted `aη, bη ←$ ℤ_p` (Eq. 13, p. 37).

**Fidelity argument.** The real game's `setup` draws `H` from `𝔾^×`
(*Nonzero crs H ←$ 𝔾^×* below), while an unrestricted pair gives `H = 0` with
probability `1/p`, one `aη` per `bη`. An adversary that acts only when `H ≠ 0`
then wins with different probabilities in the two games, so the game bridge
`AGM_UF_CMVAGame_evalDist_eq` would be false. Under the condition `H` has the
law of `uniformNonzero G` (`sign_U_dist_eq`) and `bη` is uniform and independent
of `H` (`sign_U_bu_dist_eq`), so the η coordinate of the shift point,
`log H + bη`, stays uniform and the Schwartz–Zippel argument for `3/p` is unchanged.

#### Claim 5.7: the `n → 1` collapse translates representations, not only messages

**Decision.** The Lemma 5.5 reduction `B` is built against the AGM-instrumented
UF-CMVA(+Help) game (`AlgebraicMAC.lean`), whose `Verify`/`Help` queries and
forgery carry algebraic representations over the `n`-attribute basis. `B`
therefore translates every coefficient list to the 1-attribute basis:
`AGMRepr.collapseRepr` for a single represented element and
`AGMRepr.linCombCollapse` for the `Help` arm's weighted sum `Σᵢ rᵢ • Aᵢ`
(`AttributeCollapse.lean`). The evaluation bridges, that each translation
evaluates against `(g₀, H, X₀, Xᵣ, X₁)` as the original does against
`Xᵢ = rᵢ • X₁`, are a proof obligation the paper does not have. The direction
`r⃗` is a parameter of the translations; its sampling is decided in the next
entry.

**The paper's step.** In O24 Claim 5.7 (pp. 39–40) `B` samples `zᵢ` for
`i ∈ [2, n]`, sets `Xᵢ = zᵢ X₁`, and forwards each Sign, Verify, and Help query
with the message collapsed to `m₁ + Σᵢ zᵢ mᵢ`; for Help the group-element
vector `A⃗` is collapsed to one element. Nothing else is translated, because the
plain game carries no representations.

**Rejected alternative.** Running `B` against the plain `UF_CMVAGame`, so that
only messages (and `A⃗`) collapse, exactly as in the paper.

**Fidelity argument.** The `n = 1` target `agm_ufcmva_le_n1_explicit` is stated
on the AGM game, and the AGM ↔ plain bridge is open work (#81; the
`AlgebraicMAC.lean` docstring records the gate and the deferred `WellBehaved`
bridge). Until #81 closes, a reduction to the plain game has no `n = 1` bound to
invoke, and a reduction to the AGM game must hand the 1-attribute oracles
representations they accept, hence the extra translation step and its bridges.
The step adds no adversarial power: the translated representation is computed
from the adversary's own representation and the public `r⃗`. Decided September
2026 (Track CMZ-AGM, Lemma 5.5).

#### Claim 5.7: the collapse direction is uniform in all `n` coordinates

**Decision.** The general-`n` reduction `microCMZN3DLReduction`
(`AttributeCollapse.lean`) samples the direction `r⃗ ←$ Fⁿ` uniformly in all `n`
coordinates, `r₁` included, and runs the `n = 1` reduction on the wrapper
`nTo1Adversary A r⃗`, whose `n`-attribute public parameters are `Xᵢ = rᵢ • X₁`
for every `i`.

**The paper's step.** In O24 Claim 5.7 `B` fixes `z₁ = 1` and samples `zᵢ` only
for `i ∈ [2, n]`, so the first attribute element is the 1-attribute game's `X₁`
itself and the embedded key is `(x₁, z₂x₁, …, zₙx₁)`.

**Rejected alternative.** Fixing `r₁ = 1` as the paper does and sampling the
remaining `n - 1` coordinates.

**Fidelity argument.** Both choices cost the same `1/p`, charged in the stub
`collapse_direction_averaging`: the embedded key has to be distributed as the
honest uniform `n`-attribute key, and in either case it is so exactly off the
event `x₁ = 0`. With `r₁ = 1` the key `(x₁, z₂x₁, …)` is uniform on `Fⁿ` for
`x₁ ≠ 0`; with `r⃗` fully uniform, `r⃗ · x₁` is uniform on `Fⁿ` for `x₁ ≠ 0`
because `r⃗ ↦ r⃗ · x₁` is then a bijection of `Fⁿ`. Sampling all `n` coordinates
keeps one sampler `$ᵗ (Fin n → F)` and one uniform `Xᵢ = rᵢ • X₁` clause,
instead of a distinguished index `0` in `Fin n` with its own case in every
translation. Decided September 2026 (Track CMZ-AGM, Lemma 5.5).

#### `WellBehaved` and the translation to the plain game

*Superseded.* Issue #235 replaces the gate and `WellBehaved` by an algebraic adversary type that submits coefficients only, with a forget map into the game with Help and a transfer lemma without side condition. PR #246 (part 1 of 7, approved) deletes `AGMBridge.lean`, `UFCMVA.lean` and `Core/SimulateQGuarded.lean`, and PR #247 (part 2) restricts the MAC game. The entry stays as the record of the rejected design; Semar's report of 28 October gives its timeline and cost.

**Decision.** `WellBehaved` (`AGMBridge.lean`) is the hypothesis under which the
AGM game of an algebraic adversary and the plain Figure 5 game of its
translation agree. It asks for two conditions, a never-failing run of the
oracle guarded by `agmGood` and a consistent forgery, at every key `sk`, crs
`H` and public parameters `pp`. The guard `agmGood` rejects every Help query.

O24 (p. 24) calls an adversary algebraic when it returns, with each group
element, a representation over the elements it received: a plain-game
adversary with the representations as side information. Here an algebraic
adversary is an `AGMUFAdversary` of the instrumented game, and Theorem 5.1 is
stated for its translation `AGMUFAdversary.toUFAdversary` (`AGMBridge.lean`),
which makes two choices the paper does not need. It answers a Help query with
`false` (`forgetReprImpl`). At attribute counts other than the adversary's own
`n`, it outputs the zero forgery `(fun _ => 0, (0, 0))`.

**Rejected alternatives.** (i) The two conditions only where Figure 5 samples
(O24 p. 25, `crs ← MAC.S(λ, n)` and `(sk, pp) ← MAC.K(crs)`), that is on the
supports of `setup` and `keygen`. (ii) Admitting Help queries, the oracle O24
adds after Theorem 5.1 (p. 35) for its stronger claim. (iii) An algebraic
adversary type over Sign and Verify only, so that the translation has no Help
query to answer. (iv) An algebraic adversary that runs at every attribute
count, like `UFAdversary`, so that the translation has no other count to fill.

**Fidelity argument.** (i) The bridge (#81) rewrites under the binds of
`setup` and `keygen`. It applies the never-fails condition to the transport
theorem `map_run_simulateQ_eq_of_guard_neverFails` (`Core/SimulateQGuarded.lean`)
and the consistency condition to the win bit of each reachable forgery, so it
uses both only at sampled values. Quantifying over every value keeps
`WellBehaved` a property of the adversary alone, free of the supports of
`setup` and `keygen`, as the algebraic group model states algebraicity on every
input. An adversary that computes each group element it submits from the
elements it received, with the representation it reports, meets both
conditions at every `(sk, H, pp)`.

(ii) Theorem 5.1 is stated for the Figure 5 game, whose oracles are Sign and
Verify (`UFOracleSpec`). A plain-game adversary has no Help oracle, so the AGM
adversaries that translate plain-game adversaries are those that never query
Help. The Help-strengthened claim is the Lemma 5.5 bound in the AGM game, which
keeps Help (`agm_ufcmva_le_explicit`). Help's test
`Z = (x₀ + xᵣ)A₀ + Σᵢ xᵢAᵢ` reads the μCMZ key, so it has no place in
Figure 5, which is stated for every algebraic MAC of Definition 3.1.

(iii) The Lemma 5.5 bound `agm_ufcmva_le_explicit` is stated for
`AGMUFAdversary`, whose oracles include Help, so a Help-free type would need its
own embedding into that game before the bound applies. The plain game has no
Help oracle, and the translated adversary holds no key, so it cannot compute
the Help bit and answers with a constant. `agmGood` rejects every Help query,
so under `WellBehaved` no Help query is reachable and the constant is never
read.

(iv) `UFAdversary.run` (`Core/AlgebraicMAC/Security.lean`) takes the attribute
count as an argument, because Figure 5 is stated for every algebraic MAC, while
`AGMUFAdversary F G n`, the AGM game and the reductions of Lemmas 5.4 and 5.5
are fixed at `n`. `UF_CMVAAdv` at `n` runs the translation only at `n`, where
`toUFAdversary_run` unfolds it to the algebraic adversary. The output at any
other count therefore never enters the bound, and the zero forgery is the
simplest value of the output type. Decided October 2026 (Track CMZ-AGM,
Theorem 5.1).

#### Theorem 5.10 at the honest UF-CMVA game with Help

*Status.* The game with Help is on `main` since PR #243 (merged 28 October). The bound for it is the subject of the #235 stack.

**Decision.** The unforgeability term of the Theorem 5.10 statement of #179,
`μCMZ_extractability`, is `UF_CMVAHelpAdv`
(`Schemes/MicroCMZ/UFCMVAHelp.lean`), the advantage in the honest game of Figure
5 with the oracle `Help` of §5.2, answered by the challenger with the key. No
query carries a representation, and the theorem puts no algebraic restriction on
its single-user adversary, as the printed statement puts none on its adversary.
The adversary `UFHelpAdversary` has a private coin oracle `unifSpec` beside the
game's oracles, for the reason of *One-more forgers have a private coin oracle*.
The reduction `B` of Theorem 5.10 runs the extraction adversary, whose carrier
`ZKRO H = unifSpec + H.spec` draws coins, and simulates the random oracle by
lazy sampling, so a coinless `B` could answer those queries only with fixed
values and the bound would name a family of reductions. The scope paragraph of
that entry keeps the generic `UFAdversary` coinless, and this game is specific
to μCMZ. The embedding `ufAdversaryToHelp` of a plain adversary never draws a
coin.

**Rejected alternatives.** First, the plain advantage `UF_CMVAAdv` of the Figure
5 game, which the statement of Theorem 5.1 for well-behaved algebraic
adversaries (PR #220) bounds. Its `WellBehaved` hypothesis rejects every `Help`
query, and the proof of Theorem 5.10 (§5.5) uses the answer of `Help`.
Second, the advantage `AGM_UF_CMVAAdv` in the instrumented game
`AGM_UF_CMVAGame` of `AlgebraicMAC.lean`, whose `verify` and `help` queries
carry representations. That choice forces the reduction `B` to supply
representations, which only the credential adversary holds. The theorem would
then quantify over algebraic extraction adversaries in a duplicate of `EXTGame`
with representation-carrying queries.

**Fidelity argument.** Theorem 5.1 (p. 35) is proved "even if the adversary is
given one additional oracle Help", which "will simplify the future analysis of
the keyed-verification credential scheme", and the proofs of Lemmas 5.4 and 5.5
say it "will simplify the proof of Theorem 5.11" (pp. 36, 38). The proof of
Theorem 5.10 (p. 43) uses the answer of `Help` for the first equality of its
display, and p. 42 assumes that the candidate `Z` can be checked through `Help`,
although the printed reduction `B` lists only the oracles Sign and Verify. The
term of the bound is therefore the advantage in the game with `Help`. The paper
ties `Help` to no model. The algebraic group model is a hypothesis of Theorem 5.1
and of Lemma 5.4 (pp. 35, 36), where the reduction answers `Help` from the
representations of an algebraic adversary (p. 38), and of nothing in §5.5. The
printed Theorems 5.2 and 5.10 (pp. 35, 42) put no algebraic restriction on their
adversary. The instrumented game is the device of that reduction, and its module
docstring calls it "the instrumented game, not the honest game".
`microCMZ_ufcmva_le_of_wellBehaved` of `UFCMVA.lean` bounds the plain game for
well-behaved algebraic adversaries, whose translation (`AGMBridge.lean`) answers
`help` by `false`. A bound for the game with `Help` is open, issue #235. That is
where the model enters when the two theorems are chained. `Help` reads the key
`(x₀, xᵣ, x⃗)`, so the game is specific to μCMZ and not an extension of the
generic `UF_CMVAGame` of `Core/AlgebraicMAC/Security.lean`.

### B4. Anonymity of μCMZ (O24 §5.4)

The Theorem 5.8 statement and its simulator. The printed knowledge-soundness term is under item 17 of Part A.

#### Theorem 5.8 at a fixed crs

**Decision.** The statement `μCMZ_anonymity` (`Schemes/MicroCMZ/Anonymity.lean`)
bounds `AnonAdv` at a fixed crs `H` by the §3.3 advantages of the three proof
systems viewed at that `H`. The views `riuNIZKP`, `risNIZKP` and `rpNIZKP`
attach to the proof system parameters the setup `fun _ => pure H` and the
relations `riuRel gen`, `risRel gen H` and `rpRel gen H`, through
`ProofSystemFor.toNIZKPSyntax`.

**Rejected alternative.** Views whose setup samples `H ←$ 𝔾` as the scheme's
setup does, so that `ZKAdv` and `KSNDAdv` carry the paper's sampled crs.

**Fidelity argument.** Definition 4.4 quantifies over every crs in the support
of setup and the §3.3 games sample the crs inside. A bound of a pointwise
advantage by sampled advantages does not hold in general, and
`Framework/Anonymity.lean` leaves the bridge to the theorem. Fixing the crs in
the views keeps both sides at the same `H`, and the asymptotic form over a
λ-indexed group family is issue #148.

#### The anonymity simulator takes a trace extractor

**Decision.** The extractor of `ZKP_cmz.is` that the simulator of Theorem 5.8
invokes is a `TraceExtractor` (`Core/NIZKP/Composition.lean`), a function of
the crs, the statement, the proof and the random-oracle cache. The map
`TraceExtractor.toKSND` embeds it into the
white-box `KSNDExtractor` of the knowledge-soundness game, and the lemma
`KnowledgeSound.of_trace` states that knowledge soundness with a trace
extractor implies the §3.3 notion.

**Rejected alternative.** A simulator that invokes a `KSNDExtractor`, which
takes the adversary value.

**Fidelity argument.** Definition 4.4 places `∃ Sim` before `∀ A`, so the
simulator cannot depend on the adversary. The §3.3 extractor "takes as input
the random coins and the code of the p.p.t. adversary". The proof of
Theorem 5.8 (§5.4, p. 40) has `Sim.I` invoke the extractor without resolving
the order of quantifiers, while §2.6 (p. 21) and §9 (p. 77) name the
straight-line extraction that credentials need. The §9 extractor of the
algebraic group model has the shape of a trace extractor in that it never
rewinds. It also reads the algebraic representations the
adversary supplies with every group element (Equation 41, p. 78), which are
not among the inputs of `TraceExtractor`. The instantiation of issue #3
must therefore carry the representations in the proof or in the oracle table.
The restriction keeps the printed `Adv^ksnd` applicable. Extractors carry no
running-time bound, so the restriction is a modelling discipline as long as
`OracleComp` carries no cost model, which issue #148 lists as out of scope.

### B5. One-more unforgeability and the anonymous token (O24 §5.6 and §5.2)

The game in the algebraic group model, the Theorem 5.11 statement, the forgers, the carriers and the Theorem 5.3 statement.

#### Exact-length representations in the AGM OMUF game

**Decision.** In the AGM-instrumented one-more unforgeability game for the
μCMZ_AT core (`OneMoreUnforgeability/Game.lean`) a submitted representation is
accepted only when its tag-coefficient list has exactly one entry per blinded
pair issued so far, in addition to evaluating to the submitted element
(`reprMatches`). The Sign oracle applies this gate to its *input*, the
commitment `C'` of O24 Equation 17, refusing with `none` on failure and still
logging the query together with its representation. The Verify oracle applies
the same predicate to the submitted token, like the MAC game's Verify arm but
with the exact-length rule added, so that one decidable predicate serves the
oracles and the winning condition.

**Rejected alternatives.** (i) The MAC game's convention, `AGMRepr.eval`'s
`zipWith` against the issued pairs, which ignores excess entries and reads
missing ones as zero, with no length check. (ii) Canonical normalization,
accepting any list and storing it cut to the current transcript length.
(iii) Rejecting excess entries only and accepting short lists as zero-padded.

**Fidelity argument.** The rule is a simplification, not a soundness
requirement. The Theorem 5.11 proof (O24 §5.6) substitutes each commitment's
representation into the server's answer (Equation 18) as coefficients read at
the arity of its own query, and a dictionary reading exactly that many
positions is correct on any list. Exact length buys the right to evaluate an
accepted representation against any later transcript, the final one included,
with the same result, so the winning condition and the reduction can read the
finished log against one list of pairs instead of a per-query prefix. Under
(i) an excess entry ignored at query time contributes once more pairs exist, so
the same representation names two different elements at two arities. Under
(iii) short lists are extension-stable but one coefficient vector has many list
forms, differing in omitted trailing zeros, and the reduction's coefficient
dictionary (`AGMRepr.toReprCoeffs` on the MAC side) reads an exact-length list
position by position, so exact length fixes the list form of a chosen vector
with no padding or truncation lemma. It does not make representations unique:
distinct coefficient vectors can name the same group element, which is why the
log keeps the adversary's choice. The precise guarantee is that `AGMRepr.eval`
of an accepted representation is unchanged under any later extension of the
transcript (`AGMRepr.eval_append_of_length_eq`), while `reprMatches` itself is
not, its length conjunct failing once more pairs exist. Lemmas about an
earlier commitment must evaluate its representation and never re-check the
gate at a grown transcript. The MAC game does not need the rule because its
Verify and Help representations are consumed once, at the arity of the moment
they are checked. (ii) gives the same guarantee at the cost of a normalization
lemma and is the fallback if a uniform game interface across the two tracks is
preferred.

**Why the gate cannot strengthen the adversary.** The gate is computable from
the adversary's own view, the public elements, the pairs it received, and the
representation it chose, so a refusal reveals nothing about the secret key,
and an adversary loses nothing by pre-checking its own queries. Counting
refused queries toward Figure 6's counter, rejecting short lists, and gating
the Verify arm are therefore conventions that change no adversary's power up
to a query-preserving simulation.

**What carries over from the MAC track.** The representation type `AGMRepr`,
the coefficient conversion `AGMRepr.toReprCoeffs`, and the generic
`sum_zipWith_eq_fin_sum_getD` apply to exact-length lists as they are. The
evaluation bridge `agmRepr_eval_eq_eval_toPoly` does not, since it assumes every
issued pair is a MAC tag `V = macScalar(sk, m)·U` on a known message, whereas a
blind-issuance answer is `V' = (x₀ + xᵣ)·U' + u·C'`, a polynomial in the
commitment's representation. The Equation 18 bridge is new work. Decided
September 2026 (Track CMZ-OMUF, step A4 of #12).

#### Theorem 5.11 stated before its reductions exist

**Decision.** `OneMoreUnforgeability/Statements.lean` states Theorem 5.11 (`n = 1` as
`agm_omuf_le_n1`, every `n` as `agm_omuf_le`) with `sorry` proofs in the shape
of `agm_ufcmva_le_n1_explicit`, the advantage of the forger bounded by a named
expression of the advantages of *named* reduction adversaries. The reductions
(`omufDLReduction`, `omufTwoDLReduction`, `omufGapDLReduction`) and the
attribute-lifting transformation `omufToN1` are declared as definitions whose
bodies are `sorry`, the first sorried definitions in the repository, with the
`sorry` at the whole function type. The general `n` statement follows the
paper's proof route, running the `n = 1` reductions on the transformed
adversary and adding the gap-DL reduction for the collision case.

**Rejected alternatives.**

- *Existential quantification over the reductions* ("there exist B, B₂ with
  Adv(A) ≤ …"). Vacuous at fixed parameters: the discrete logarithm relative to
  a generator is a function on a finite group, so a perfect solver exists with
  advantage 1, and the right-hand side then exceeds every probability.
- *A uniform bound ε on every discrete-log adversary as hypothesis.* False
  below 1 for the same solver, trivial at 1 or above.
- *`sorry` under the binders* (`def f (A) := sorry`). Makes `f A₁ = f A₂` hold
  by `rfl`, an accidental input-independence later proofs could lean on.
- *Fresh reduction stubs at arity `n`* for the general statement, neutral
  about the proof. Rejected for now in favour of the paper's route, which
  keeps the number of declarations with `sorry` bodies smaller and makes the transformation the concrete
  object of the open question whether it reuses the Lemma 5.5 embedding.

**Constraints recorded.** No lemma may be stated about a sorried stub beyond
the theorems that cite it, since anything provable about an unspecified body
holds of every inhabitant. The discrete-log reduction takes the Sign budget
`q`, which a selector over the `q` issuance positions of Claim 5.12 needs. The
adversary has a private coin oracle (*One-more forgers have a private coin
oracle*), so the transformation samples through it. Extra Sign queries are not
a source of randomness, they break the budget and the one-more count.

**Per-Claim reductions.** Claims 5.12 and 5.13 each name their own discrete-log
reduction, `omufDLReductionU gen q A` (the selector over the `q` issuance
positions, bound `q·(1/p + Adv)`) and `omufDLReductionEta gen A` (the challenge
in the crs, bound `1/p + Adv`), while Claim 5.14 cites the theorem's
`omufTwoDLReduction`. The theorem's `omufDLReduction` is then the mixture of the
two, run with probabilities `q/(q + 1)` and `1/(q + 1)`, so that
`(q + 1)·Adv(mixture) = q·Adv(B_U) + Adv(B_η)` and the three Claims add up to
Equation 23. The paper leaves this step implicit, writing `(q + 1)·Adv^dl` for
the reductions of Claims 5.12 and 5.13 without naming an adversary, and the
mixture makes that sum precise. Only Claim 5.12 carries the budget hypothesis, since only its
constant is the budget. A shared discrete-log stub cited by both Claims was
rejected. Its natural body is a `(q + 1)`-way selector over the `q` positions
and the crs, which supports the factor `q + 1` in each Claim, not the paper's
`q` and `1`. The case events are the paper's formal items. The extraction
obligation recorded in the module docstring of `Statements.lean`, that a
monomial's coefficient remain nonzero after the evaluation of the other
variables at the run's values, with an example where it does not, may move the
Claims to
evaluated events or add a Verify budget to the statements, a decision left to
the proof phase.

#### One-more forgers have a private coin oracle

**Decision.** Both one-more unforgeability adversaries have a private coin
oracle beside the game's oracles. The plain `OMUFAdversary` runs in
`OracleComp (unifSpec + OMUFOracleSpec tok crs)`, the algebraic
`AGMOMUFAdversary` in `OracleComp (unifSpec + AGMOMUFOracleSpec F G n)`.
`OMUFGame` and `AGM_OMUFGame` answer the private coin oracle in `ProbComp`, and
the budget predicate `AGMOMUFQuery.isSign` counts Sign queries only.

**Rejected alternative.** *Fixed coins in the construction*, the adversary
types without a private coin oracle. A transformation that needs randomness
then takes its coins as an argument, and its proof needs a fixed-coins
argument. This is the route of Lemma 5.5, whose `nTo1Adversary gen A r` takes
the direction `r⃗` as an argument while `microCMZN3DLReduction` samples it, and
it serves there because no forger the MAC track builds appears in its bounds.
The `π_is` lifting lemma of #205 names the forger it builds in its bound, so
fixed coins would make that term an average over a family of forgers, and that
forger's coins, a lazily sampled random oracle and one simulator run per Sign
query, are not a fixed tuple.

**Fidelity argument.** O24's algorithms are p.p.t. with random coins (§3,
*Notation*), and Figure 6 runs its adversary on `pp` alone, so the coins are
its own. An `OracleComp` computation draws randomness only by querying an
oracle. VCV-io's PRF, IND-CPA and Fischlin adversaries have a private coin
oracle beside the game oracles (`PRFOracleSpec`, `IND_CPA_oracleSpec`, and the
Fischlin adversaries put `unifSpec` first), and a transformation then samples
inside the adversary it builds, as VCV-io's Fiat–Shamir `simulatedNmaAdv` runs
its simulator inside the adversary it builds. The formal forger class contains
the paper's and is larger: a p.p.t. forger is an inhabitant, each of its
`A.rl(λ)` coins a `unifSpec` query at index 1, while `OracleComp` bounds no
running time and `unifSpec` answers a query at index `n` with an exactly
uniform element of `Fin (n + 1)`, for any `n` and any number of queries.

**Scope.** The UF-CMVA forgers `UFAdversary` and `AGMUFAdversary` keep their
shape, without a private coin oracle. The algebraic one-more forger has the
oracle with the plain one because the bridge from the algebraic to the plain
game maps an algebraic forger to a plain one, and a plain forger that samples,
such as the one the lifting lemma of #205 builds, is such an image only if the
algebraic forger samples too. Decided October 2026 (Track CMZ-OMUF, #205).

#### Two carriers for one-more unforgeability

**Decision.** Anonymous tokens keep two carriers. The core μCMZ_AT and the
plain Figure 6 game stay at `ProbComp`. A scheme whose server attaches a
Fiat–Shamir proof, such as the printed μCMZ_AT with `π_is`, runs at
`OracleComp (ZKRO H)` and gets its own game, `OMUFGameRO`, which runs through
one `runRO` from the empty cache, so the scheme's proofs and the adversary's
hash queries share it (`AnonymousTokens/OracleCarrier.lean`). Both games run
one experiment, `omufExp`, generic in the carrier `OracleComp spec`, over a
query type, oracle, log and winning condition generic in the monad. One bridge
relates them: `ATSyntax.toZKRO` lifts a `ProbComp` scheme through `liftM`,
`OMUFAdversary.toZKRO` lifts an adversary, and `OMUFAdvRO_toZKRO` equates the
lifted advantage with the `ProbComp` one.

**Why.** The `π_is` lifting lemma of #205 bounds the scheme with `π_is` by the
core, so its left side lives at the oracle carrier and its right side at
`ProbComp`; the bridge is the step between them. With the experiment generic
in the carrier, `OMUFGame` and `OMUFAdv` are `ProbComp` definitions, and every
statement over them is a `ProbComp` statement.

**Rejected alternatives.**

- *One game over every carrier*, `OMUFGame` itself generic. A game ends in
  `ProbComp`, so a generic one needs a way to run its carrier to `ProbComp`,
  `runRO` with its cache for one carrier and the identity for the other; with
  the experiment `omufExp` generic instead, each carrier's game supplies its
  own runner in one line (`runRO H ∅` at the oracle carrier, none at
  `ProbComp`).
- *A copy of the declarations for the oracle carrier.* The same declarations
  twice, with nothing to keep them in step. Only the adversary structure is
  restated per carrier: `OMUFAdversaryRO` is `OMUFAdversary` with `ZKRO H` in
  place of `unifSpec`.
- *VCV-io's `evalDist_liftComp` for the bridge.* It needs `IsUniformSpec` on
  both specifications, which `ZKRO H` lacks, and it reads a computation through
  `evalDist`, where every query, a repeated `H` query included, is an
  independent draw. The game answers `H` through the cache of `runRO`, so a
  repeated query gets the same answer, and the bridge is an equation between
  games run through `runRO`, the setting of `runRO_liftM`.

Decided October 2026 (Track CMZ-OMUF, #183).

#### Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11

*Status.* On the branch `microcmz-theorem-5-3`, not on `main`. The one-more unforgeability clause of the branch is on the plain game of Figure 6 and quantifies over every adversary, which claims more than the paper proves. On 28 October the decision was taken to state that clause in the algebraic group model as printed, which needs a game in that model for the scheme with π_is, a prerequisite of the size of #181. Issue #184 is postponed until that game exists, summary on #184.

**Decision.** The Theorem 5.3 statement (#184) is the conjunction of
correctness, anonymity and one-more unforgeability of μCMZ_AT, with each
clause as the theorem it derives from states it, p. 35 "From the above, and
Theorem 5.11". Four points.

1. *The bounds.* Anonymity is bounded by Adv^zk_cmz.p + Adv^ksnd_cmz.is, the
   printed Adv^zk_cmz.iu dropped (errata item 18). One-more unforgeability is
   bounded by `omufBound` of Theorem 5.11 plus Adv^zk_cmz.is, the printed
   Adv^2dl + q·Adv^dl + (q+5)/p replaced (errata item 19) and the `π_is` term
   added (errata item 7).
2. *The anonymity clause.* Definition 4.4 (`AnonAdv`) on μCMZ_AT as a
   `KVACSyntax` at the oracle carrier, the issuance of Figure 9 without `π_iu`
   and the presentation of μCMZ, with the Theorem 5.8 simulator
   `μCMZAnonSimulator` without its `π_iu` simulator, under the Remark 5.9
   hypotheses of `μCMZ_anonymity` for `π_is` and `π_p` alone.
3. *The one-more unforgeability clause.* The game of Figure 6 at the oracle
   carrier, `OMUFAdvRO` on `μCMZATSyntax`, the game of the definition of an
   anonymous token (§3.4), with the Sign budget `q` as a hypothesis counted
   by `OMUFQueryRO.isSign`. The term for `π_is` is the zero-knowledge
   advantage of the named reduction `omufPiIsZKAdversary`, declared with a
   `sorry` body, which the lifting lemma of #205 defines without changing the
   statement. The three `omufBound` reductions take the simulator of `π_is`
   as well, since the lifted forger they run on attaches its simulated
   proofs. The words "in the algebraic group model" of the print are not a
   hypothesis of the Lean statement. Theorem 5.11 is proved in that model,
   and its game `AGM_OMUFGame` runs the core without `π_is`, while the
   repository has no notion of an algebraic adversary for the scheme with
   `π_is`, whose issuer sends proofs that may carry group elements outside
   the basis of that game. So the sorried clause claims the bound for every
   adversary of Figure 6, more than the paper proves. The restriction returns
   with the bridge from the game of Theorem 5.11 to the plain game on the
   core, which the proof of the clause needs, together with an argument that
   the simulated `π_is` keep the forger algebraic over that basis.
4. *The group.* Fixed `F` and `G`, the clause "n = poly(λ)" left to #148, as
   for Theorems 5.2, 5.8 and 5.10.

Two further points follow from the first two.

- *No Remark 5.9 hypotheses.* `μCMZ_anonymity` carries the condition of
  Remark 5.9 as region hypotheses, since hybrid H3 extracts from a `π_is`
  produced after the simulated `π_iu` of H1. The token's user sends `C'`
  alone, no simulated proof precedes the issuer's `π_is`, and hybrid H2
  simulates `π_p` after issuance has ended. The anonymity clause therefore
  takes the printed `Adv^ksnd` without those hypotheses.
- *The blueprint node of the printed theorem.* The node `mucmz_at_omuf`
  names no Lean declarations, since the Lean statement is the corrected one,
  per the honesty rule of `docs/BLUEPRINT_MAINTENANCE.md` and the plan Jin
  sent to Rolfe on 20 August 2026 (errata item 7). Its proof cites the
  milestone node `mucmz_at_anonymous_token`, which names the theorem.

**Rejected alternatives.**

- *The printed bounds.* No version of the paper proves the printed one-more
  unforgeability bound, and the printed anonymity term charges a proof the
  scheme does not produce. Keeping them would state a theorem the cited proofs
  do not establish.
- *A sorried unlinkability predicate on `ATSyntax`.* §3.4 (p. 26) omits the
  definition of unlinkability and keeps "the stronger anonymity properties",
  so the anonymity clause is Definition 4.4, not a new notion.
- *The game of Theorem 5.11, `AGM_OMUFAdv` on `AGMOMUFAdversary`, as the
  one-more unforgeability target.* That game runs the core without `π_is`,
  so the clause would be about a scheme other than the one Theorem 5.3
  defines, the choice errata item 7 rules out. A game in the algebraic group
  model for the scheme with `π_is` is new work of the size of #181, beyond a
  statement with `sorry`.
- *Waiting for the author's correction before the π_is-carrying instance and
  the lifting lemma*, the plan of 20 August. The instance (#183) and the
  lemma (#205) proceed, and the errata record the departure from the print.

**Fidelity argument.** Theorem 5.3 is a corollary, p. 35, so its faithful
statement is what its two sources establish for the scheme defined on p. 35,
μCMZ_AT with `π_is`, in the game of the definition of §3.4. Every departure
from the print is an errata item.

Decided 28 October 2026 (Track CMZ-OMUF, #184).

### B6. Open alternatives

**The crs and the group.** In the paper `μCMZ.S(1^λ, n)` runs `GrGen(1^λ)`
and returns `crs := (Γ, H)`, the group description together with a random
group element (Figure 9). The μCMZ instance fixes the group and its generator
as type parameters and returns only `H` from `setup`, so the framework's
quantifier "crs ∈ [KVAC.S(1^λ, n)]" ranges over every group of the class and
every nonzero `H` (#149), with no λ in it. The faithful crs is `Γ × 𝔾`. Issue
#148 tracks the encodings, a deterministic family `GrGen : ℕ → Type` as the
committed step, and sampled group descriptions as the fully faithful one.
Until it closes the asymptotic predicates `Anonymous`, `AnonymousPoly`,
`Extractable` and `ExtractablePoly` are not provable for μCMZ, and the
theorems bound the advantages at fixed parameters.

**Adversary classes and the paper's p.p.t. class** (issue #240, open). Every
adversary of the formalization is an `OracleComp` computation, with no running
time, and the repository defines no p.p.t. predicate. Under a "for all
adversaries" quantifier the wider class makes a theorem stronger, under a
"there exists a simulator or extractor" quantifier it makes a definition
weaker, so simulators and extractors are named or carry an efficiency
predicate. The one-more forgers have a private coin oracle since PR #232, so
their class contains the paper's. The UF-CMVA forgers, the extractors and the
efficiency parameters `isPPT` are not yet classified. The running-time bound of
the simulator of Definition 4.4 and of the extractor of Definition 4.5 is the
formalization's choice, O24 fixing none, decided by what the Lean proofs of
Theorems 5.8 and 5.10 establish.

## Where the items are recorded in the code

The closing paragraph of the errata, as it stands on the branch.

Items 16 and 17 concern §5.4 and are recorded in `docs/DESIGN_ALTERNATIVES.md`
and in `Schemes/MicroCMZ/Anonymity.lean`. Items 18 and 19 concern §5.2 and are
recorded on issue #184 and in the Theorem 5.3 statement.
The corrections to Eqs. 13/14 are visible today in the open PR #88 diff
(module `AGMReduction/Core`); the remaining §5.3 items are documented in the
reduction modules queued behind it, in the order shown on the
presentation's architecture slide. Item 7 concerns §5.6 and is recorded in
`docs/DESIGN_ALTERNATIVES.md` and at its use sites in
`Schemes/MicroCMZ/ATVariant.lean`. Item 8 concerns all of Figure 9. The
credential in `Schemes/MicroCMZ/Credential.lean` records it at the three draws,
and the anonymous-token core in `Schemes/MicroCMZ/ATVariant.lean` at the two
issuance nonces. The header of `Framework/Correctness.lean` records its effect
on correctness. Items 5 and 9–11 are recorded at their
use site in `Schemes/MicroCMZ/AGMReduction/GapDLReduction.lean`. Item 12 is
recorded in `Schemes/MicroCMZ/OneMoreUnforgeability/Statements.lean`. Items
13–15 concern §5.1 and §5.4: item 13 is recorded in
`docs/DESIGN_ALTERNATIVES.md` and at `setup` in
`Schemes/MicroCMZ/Construction.lean`; items 14 and 15 are requirements on the
simulator under #163. This note
reports findings about the paper; the formal-completion status of each module is tracked on the
project's blueprint page.

Items 18 and 19 and the entry on Theorem 5.3 are on the branch
`microcmz-theorem-5-3` and on issue #184. The candidates P16 to P22 are
documented in `docs/CRYPTOGRAPHIC_PROOFS_MICROCMZ_LEMMA55.md`, P16 also at
`gapDlOracleImpl` (`Schemes/MicroCMZ/AGMReduction/GapDLReduction.lean`), P18 at
`Schemes/MicroCMZ/AGMReduction/AttributeCollapse.lean` and P22 at `mac`
(`Schemes/MicroCMZ/Construction.lean`). S1 is recorded at `exponentEval`
(`Schemes/MicroCMZ/AGMReduction/Core.lean`) and S2 in the design entry
*Theorem 5.10 at the honest UF-CMVA game with Help*.
