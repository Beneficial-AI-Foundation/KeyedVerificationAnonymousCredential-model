# Errata to O24 §5.3 and §5.6, found while constructing the Theorem 5.1 and Theorem 5.3 reductions

Companion note to the status presentation (2026-07-30). Paper: Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
("O24"), as `docs/Orru_2024.pdf`. Each item below is a discrepancy between the
paper's printed §5.3 or §5.6 material and what the reduction, worked in full
detail, actually requires. Every item is checkable by hand against the paper; none
weakens the result — the assumptions are the paper's own; one unjustified
summand is dropped (item 2) and the additive constant changes (3/p → 5/p,
both ≈ 2<sup>−250</sup> at ristretto255).

## 1. The 1/p non-vanishing bound should be 3/p (p. 38)

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

## 2. Lemma 5.4's printed Adv<sup>dl</sup> summand has no reduction behind it (pp. 36–38)

Lemma 5.4 (p. 36) states the single-attribute bound as
Adv<sup>3-dl</sup> + Adv<sup>dl</sup> + 1/p. Its proof (pp. 36–38) builds
one reduction, to 3-DL: the public parameters and the signing responses are
embedded off the 3-DL instance (Eqs. 13–14), and the forgery is turned into a
root of the affinely-substituted polynomial ψ, which is the 3-DL solution.
No DL reduction appears, so the Adv<sup>dl</sup> summand is unjustified by the
proof and survives only as nonnegative slack. The formalized statement
(`agm_ufcmva_le_n1_explicit`) bounds the advantage by
Adv<sup>3-dl</sup> + 3/p, with the constant from item 1.

## 3. Eq. 13: X₀'s X-coefficient (typo)

Eq. 13 defines the affine embedding of the public parameters off the 3-DL
instance (X, X′, X″). The paper prints X₀'s X-coefficient as
a<sub>h</sub>b₀ + b<sub>h</sub>. Expanding X₀ = x₀·H under the affine
substitution v ↦ a<sub>v</sub> + x·b<sub>v</sub> gives the X-coefficient

&nbsp;&nbsp;&nbsp;&nbsp;a₀b<sub>h</sub> + b₀a<sub>h</sub>,

i.e. the printed version drops the a₀ factor. The corrected coefficient is
documented at its use site in the reduction-core module under review
(PR #88, `AGMReduction/Core.lean`, docstring at the Eq. 13 embedding).

## 4. Eq. 14: signing-response coefficient (typo)

Eq. 14 gives the simulated signing response's coefficient. The paper prints
the factor as a·uⱼ·(a<sub>h</sub>a₀ + a<sub>h</sub> + mⱼa₁); the correct
factor is

&nbsp;&nbsp;&nbsp;&nbsp;A = a₀ + a<sub>r</sub> + a₁mⱼ,

the key polynomial's constant part evaluated at the queried message. Also
documented at its use site in PR #88.

## 5. Claim 5.6's extraction has the wrong sign (p. 39)

From a collision Σᵢ mⱼ,ᵢ(aᵢG + bᵢX) = Σᵢ m*ᵢ(aᵢG + bᵢX) the paper derives
(Σᵢ (mⱼ,ᵢ − m*ᵢ)aᵢ)G = (Σᵢ (mⱼ,ᵢ − m*ᵢ)bᵢ)X and returns
x = (Σᵢ aᵢ(mⱼ,ᵢ − m*ᵢ))(Σᵢ bᵢ(mⱼ,ᵢ − m*ᵢ))<sup>−1</sup>. Moving the X-terms
across flips their sign, so the relation is
(Σᵢ (mⱼ,ᵢ − m*ᵢ)aᵢ)G = −(Σᵢ (mⱼ,ᵢ − m*ᵢ)bᵢ)X and the printed value is −x.
The correct extraction is

&nbsp;&nbsp;&nbsp;&nbsp;x = (Σᵢ aᵢ(m*ᵢ − mⱼ,ᵢ))(Σᵢ bᵢ(mⱼ,ᵢ − m*ᵢ))<sup>−1</sup>,

documented at its use site (`gapDlReduction` in
`AGMReduction/GapDLReduction.lean`).

## 6. Theorem 5.1's printed bound elides the gap-DL term

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

## 7. Figure 9 boxes only π<sub>iu</sub>, but the Theorem 5.11 proof analyzes the scheme without π<sub>is</sub> (pp. 34–35, 40, 44)

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
(`Schemes/MicroCMZ/ATVariant.lean`, PR #147) and defers the
π<sub>is</sub>-carrying variant and the lifting lemma to Phase B of the
Theorem 5.3 plan (issue #12). Reported to the author in August 2026.

## 8. Figure 9 samples r ←$ ℤ<sub>p</sub>, but §5.1 requires r ≠ 0 (pp. 33–34)

Figure 9's unblinding step samples the user re-randomizer as r ←$ ℤ<sub>p</sub>.
§5.1 (p. 33) states the re-randomization property for r ≠ 0, and the
presentation step samples the same operation with r ←$ ℤ<sub>p</sub><sup>×</sup>.
An honest run with r = 0 emits the token (0, 0), which the scheme's own
verifier rejects. Same family as the U ←$ 𝔾 versus Eq. (1) U ←$ 𝔾<sup>×</sup>
mismatch for the base MAC. Under the literal samplers honest issuance fails
with probability 2/p − 1/p<sup>2</sup> (u = 0 aborts at the user's check,
r = 0 mis-issues). The formalization draws both nonces from
ℤ<sub>p</sub><sup>×</sup> (`uniformUnits`, PR #146 and PR #147).

## 9. Claim 5.6 never defines X<sub>r</sub> (p. 39)

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

## 10. Claim 5.6's Verify query drops the Σᵢ aᵢmᵢ term (p. 39)

For Σᵢ bᵢmᵢ ≠ 0 the printed Verify answer is the bit of
Ddh(U, (Σᵢ bᵢmᵢ)<sup>−1</sup>V − zU). Its Σᵢ bᵢmᵢ = 0 branch checks
zU + Σᵢ aᵢmᵢU = V, and the signing answer uses (z + Σᵢ aᵢmᵢ)U, but the Ddh
argument subtracts only zU. With d = Σᵢ bᵢmᵢ the honest equation
V = (c + x·d)U needs the full constant part c·U removed (item 9 adds the
x<sub>r</sub> term).

## 11. Claim 5.6's Verify query misplaces the inverse (p. 39)

The printed argument (Σᵢ bᵢmᵢ)<sup>−1</sup>V − zU applies d<sup>−1</sup> to V
alone. Solving V = (c + x·d)U for the DH value gives d<sup>−1</sup>(V − cU) =
x·U, so the query must be

&nbsp;&nbsp;&nbsp;&nbsp;Ddh(U, d<sup>−1</sup>(V − cU)).

The formalization avoids the inverse by querying Ddh(d·U, V − c·U), which
returns the same bit for d ≠ 0 and also subsumes the d = 0 branch
(`gapDlOracleImpl`, `AGMReduction/GapDLReduction.lean`).

## 12. Claim 5.13's bound has no term for Verify queries (pp. 46–47)

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

## 16. Hybrid H2 of Theorem 5.8 charges ZKP<sub>cmz.iu</sub> for the simulation of π<sub>p</sub> (p. 41)

Items 13 to 15 are added by #149. Hybrid H2 (p. 41) replaces π<sub>p</sub>
by the output of the zero-knowledge simulator of ZKP<sub>cmz.p</sub>, and its
displayed bound reads
Adv<sup>H2</sup> ≥ Adv<sup>H1</sup> − Adv<sup>zk</sup><sub>ZKP<sub>cmz.iu</sub>,D′</sub>,
with the subscript of H1. The system whose zero knowledge the step uses is
ZKP<sub>cmz.p</sub>, as the statement of Theorem 5.8 (p. 40) prints it. The
statement `μCMZ_anonymity` in `Schemes/MicroCMZ/Anonymity.lean` charges the
second term to ZKP<sub>cmz.p</sub>.

## 17. Theorem 1 prints Adv<sup>simex</sup> where Theorem 5.8 prints Adv<sup>ksnd</sup> (pp. 4, 40, 42)

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
"the vector sizes mismatch", without a proof. No prose connects Theorem 1 and
Remark 5.9. The formalization keeps the printed Theorem 5.8 and states the
Remark as the lemma `ksndSimAdv_le_ksndAdv_of_domainSeparated` in
`Core/NIZKP/Composition.lean`, with the mismatch as an explicit region of the
random-oracle domain.

## Status

Items 16 and 17 concern §5.4 and are recorded in `docs/DESIGN_ALTERNATIVES.md`
and in `Schemes/MicroCMZ/Anonymity.lean`.
The corrections to Eqs. 13/14 are visible today in the open PR #88 diff
(module `AGMReduction/Core`); the remaining §5.3 items are documented in the
reduction modules queued behind it, in the order shown on the
presentation's architecture slide. Items 7 and 8 concern §5.6 and are
recorded in `docs/DESIGN_ALTERNATIVES.md` and at their use sites in
`Schemes/MicroCMZ/ATVariant.lean`. Items 5 and 9–11 are recorded at their
use site in `Schemes/MicroCMZ/AGMReduction/GapDLReduction.lean`. Item 12 is
recorded in `Schemes/MicroCMZ/OneMoreUnforgeability/Statements.lean`. This note
reports findings about the paper; the formal-completion status of each module is tracked on the
project's blueprint page.
