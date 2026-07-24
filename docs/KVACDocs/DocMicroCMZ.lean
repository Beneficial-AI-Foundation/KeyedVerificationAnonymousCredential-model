/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import KVAC.Schemes.MicroCMZ.Construction
import KVAC.Schemes.MicroCMZ.Relations
import KVAC.Schemes.MicroCMZ.AGMPolynomial
import KVAC.Schemes.MicroCMZ.AlgebraicMAC
import KVAC.Schemes.MicroCMZ.SignMask

open Verso.Genre Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true


#doc (Manual) "μCMZ" =>
%%%
tag := "microcmz"
%%%

The first concrete instantiation of the abstract framework, corresponding
to O24, Section 5. μCMZ improves on Chase–Meiklejohn–Zaverucha (2014):
O(1) issuance cost (down from O(n)), statistical anonymity, and security
in the algebraic group model under 3-DL. Deployed by Signal, Tor, and
NYM.

Five files under `KVAC/Schemes/MicroCMZ/`:

- `Construction.lean` — Section 5.1 — Track CMZ-C.
- `AlgebraicMAC.lean` — Section 5.3 — Track CMZ-M.
- `Anonymity.lean` — Section 5.4 — Track CMZ-A.
- `Extractability.lean` — Section 5.5 — Track CMZ-E.
- `OneMoreUnforgeability.lean` — Section 5.6 — Track CMZ-OMUF.

:::theorem "mucmz_is_kvac" (tags := "paper, O24 Thm 1") (effort := "small") (priority := "medium")
*O24 Theorem 1.* μCMZ is a keyed-verification anonymous credential
system: extractable ({uses "mucmz_extractable_kvac"}[]) and one-more unforgeable as an
anonymous token ({uses "mucmz_at_omuf"}[]) in the algebraic group model, with
the stated advantage bounds.
:::

# Construction (Section 5.1)

:::group "cmz_construction"
μCMZ construction
:::

The four protocol algorithms: `KeyGen`, `Setup`, `Issue` (with predicate
`φ`), and `Present`. Stated over the abstract `PrimeOrderGroup F G` —
no curve, hash function, or deployment is committed to here.

The base MAC of the construction is merged; the credential protocol
around it (Issue and Present, the predicate flow) remains open, per the
scope note in `Construction.lean`'s module docs.

*TODO (Track CMZ-C).* Implement Issue and Present following Section 5.1,
on top of the merged base MAC.

:::definition "mucmz_base_mac" (lean := "KVAC.Schemes.MicroCMZ.Params, KVAC.Schemes.MicroCMZ.Key, KVAC.Schemes.MicroCMZ.Code, KVAC.Schemes.MicroCMZ.keygen, KVAC.Schemes.MicroCMZ.setup, KVAC.Schemes.MicroCMZ.macScalar, KVAC.Schemes.MicroCMZ.mac, KVAC.Schemes.MicroCMZ.verify, KVAC.Schemes.MicroCMZ.μCMZBaseMACSyntax, KVAC.Schemes.MicroCMZ.μCMZBaseMAC, KVAC.Schemes.MicroCMZ.μCMZBaseMAC_correct, KVAC.Schemes.MicroCMZ.uniformNonzero, KVAC.Schemes.MicroCMZ.mem_support_uniformNonzero, KVAC.Schemes.MicroCMZ.instSampleableTypeNeZero") (parent := "cmz_construction") (tags := "milestone")
The μCMZ base MAC over an abstract prime-order group
({uses "sampleable_group"}[]): key sampling, the scalar-side MAC
`V = (x₀ + xᵣ + m·x₁)·U` with a nonvanishing tag base, deterministic
verification, and the packaging as an algebraic MAC
({uses "algebraic_mac"}[]) with its correctness proof.
:::

:::definition "mucmz_policy_layer" (lean := "KVAC.Schemes.MicroCMZ.Policy, KVAC.Schemes.MicroCMZ.PublicBases, KVAC.Schemes.MicroCMZ.Enforces, KVAC.Schemes.MicroCMZ.trivialPolicy, KVAC.Schemes.MicroCMZ.riu_enforces_trivialPolicy, KVAC.Schemes.MicroCMZ.rp_enforces_trivialPolicy") (parent := "cmz_construction") (tags := "milestone")
Credential policies `φ` over attribute vectors, the public issuer bases,
the enforcement predicate connecting a relation to its policy, and the
trivial policy with its enforcement lemmas.
:::

:::theorem "mucmz_sigma_protocols" (lean := "KVAC.Schemes.MicroCMZ.riuSigma, KVAC.Schemes.MicroCMZ.riuSigma_complete, KVAC.Schemes.MicroCMZ.riuSigma_hvzk, KVAC.Schemes.MicroCMZ.riuSigma_speciallySoundAt, KVAC.Schemes.MicroCMZ.riuSigma_speciallySoundAt_trivial, KVAC.Schemes.MicroCMZ.riuSimTranscript, KVAC.Schemes.MicroCMZ.risSigma, KVAC.Schemes.MicroCMZ.risSigma_complete, KVAC.Schemes.MicroCMZ.risSigma_hvzk, KVAC.Schemes.MicroCMZ.risSigma_speciallySound, KVAC.Schemes.MicroCMZ.risSimTranscript, KVAC.Schemes.MicroCMZ.rpSigma, KVAC.Schemes.MicroCMZ.rpSigma_complete, KVAC.Schemes.MicroCMZ.rpSigma_hvzk, KVAC.Schemes.MicroCMZ.rpSigma_speciallySoundAt, KVAC.Schemes.MicroCMZ.rpSigma_speciallySoundAt_trivial, KVAC.Schemes.MicroCMZ.rpSimTranscript") (parent := "cmz_construction") (tags := "milestone")
Interactive Σ-protocols for the three relations {uses "riu_relation"}[],
{uses "ris_relation"}[], and {uses "rp_relation"}[], each with
completeness, honest-verifier zero-knowledge via an explicit simulated
transcript, and special soundness, over a {uses "sampleable_group"}[]
carrier. Their Fiat–Shamir compilation into a `NIZKPSyntax` is future
work (see the *Proof systems* chapter).
:::

:::proof "mucmz_sigma_protocols"
Each protocol commits with fresh uniform masks, responds linearly
(`z = ρ + c·w`), and verifies the corresponding linear identity.
Completeness is algebra; honest-verifier zero-knowledge samples the
response first and solves for the commitment; special soundness
subtracts two accepting transcripts.
:::

:::definition "mucmz_construction" (parent := "cmz_construction") (tags := "paper, O24 Fig 9")
*O24 Figure 9.* The μCMZ keyed-verification credential system
construction (a variant of `MAC_GGM`), instantiating the KVAC syntax
{uses "kvac_syntax"}[] from an algebraic MAC {uses "algebraic_mac"}[]; the boxed
part is removable for the one-more unforgeable variant. The MAC side is
merged as {uses "mucmz_base_mac"}[]; Issue and Present remain open.
:::

:::definition "riu_relation" (lean := "KVAC.Schemes.MicroCMZ.RiuStmt, KVAC.Schemes.MicroCMZ.RiuWitness, KVAC.Schemes.MicroCMZ.riuRel") (parent := "cmz_construction") (tags := "paper, O24 Eq 9")
*O24 Equation 9.* `R_iu`, the μCMZ issuance user-proof relation of
{uses "mucmz_construction"}[]: knowledge of an opening of the attribute commitment
`C'` satisfying the policy `φ` ({uses "mucmz_policy_layer"}[]).
:::

:::definition "ris_relation" (lean := "KVAC.Schemes.MicroCMZ.RisStmt, KVAC.Schemes.MicroCMZ.RisWitness, KVAC.Schemes.MicroCMZ.risRel") (parent := "cmz_construction") (tags := "paper, O24 Eq 10")
*O24 Equation 10.* `R_is`, the μCMZ issuance server-proof relation of
{uses "mucmz_construction"}[]: knowledge of `(x₀, u)` consistent with the issuer
parameters and the returned tag.
:::

:::definition "rp_relation" (lean := "KVAC.Schemes.MicroCMZ.RpStmt, KVAC.Schemes.MicroCMZ.RpWitness, KVAC.Schemes.MicroCMZ.rpRel") (parent := "cmz_construction") (tags := "paper, O24 Eq 11")
*O24 Equation 11.* `R_p`, the μCMZ presentation-proof relation of
{uses "mucmz_construction"}[]: knowledge of `(r', r⃗, m⃗)` opening the presentation
commitments over `U'` and `Z`, with the policy `φ`
({uses "mucmz_policy_layer"}[]) satisfied.
:::

# Algebraic-MAC security (Section 5.3)

:::group "cmz_amac"
μCMZ MAC security
:::

*Theorem 5.1.* μCMZ, viewed as an algebraic MAC under the *Core*
algebraic-MAC interface, is UF-CMVA in the algebraic group model under
3-DL. The proof factors through two lemmas:

- *Lemma 5.4* — the `n = 1` attribute case,
- *Lemma 5.5* — the general `n`-attribute case, lifted from Lemma 5.4.

This is the load-bearing security result for μCMZ; both extractability
(Section 5.5) and the anonymous-token one-more unforgeability (Section
5.6) factor through it.

The Lemma 5.4 workshop is merged: the AGM game, the verification
polynomial with its identity case, and the sign-mask distribution
lemmas. The assembly of Lemma 5.4 from these pieces (the `AGMReduction`
game bridge, including the ≤3-roots bound and the ψ ≠ 0 argument) is in
flight.

*TODO (Track CMZ-M).* Assemble Lemma 5.4 from the merged workshop
pieces, then state Lemma 5.5 and Theorem 5.1.

:::definition "agm_model" (lean := "KVAC.Schemes.MicroCMZ.AGMRepr, KVAC.Schemes.MicroCMZ.AGMRepr.eval, KVAC.Schemes.MicroCMZ.AGMQuery, KVAC.Schemes.MicroCMZ.AGMOracleSpec, KVAC.Schemes.MicroCMZ.AGMLog, KVAC.Schemes.MicroCMZ.agmOracleImpl, KVAC.Schemes.MicroCMZ.AGMUFAdversary, KVAC.Schemes.MicroCMZ.AGM_UF_CMVAGame, KVAC.Schemes.MicroCMZ.AGM_UF_CMVAAdv, KVAC.Schemes.MicroCMZ.glog, KVAC.Schemes.MicroCMZ.glog_smul, KVAC.Schemes.MicroCMZ.glog_smul_self, KVAC.Schemes.MicroCMZ.glog_add, KVAC.Schemes.MicroCMZ.glog_smul_scalar, KVAC.Schemes.MicroCMZ.gen_ne_zero") (parent := "cmz_amac") (tags := "milestone")
The UF-CMVA game of {uses "ufcmva_game"}[] specialised to algebraic
adversaries against the single-attribute base MAC
({uses "mucmz_base_mac"}[]): adversaries return AGM representations for
every output group element, oracles gate on representation consistency,
and the discrete-log bookkeeping runs through `glog` with its linearity
laws, over a {uses "sampleable_group"}[] carrier.
:::

:::theorem "identity_case_lem54" (lean := "KVAC.Schemes.MicroCMZ.AGMPoly.spec, KVAC.Schemes.MicroCMZ.AGMPoly.identity_case, KVAC.Schemes.MicroCMZ.AGMPoly.toPoly_eq_zero_of_verifPoly_eq_zero") (parent := "cmz_amac") (tags := "milestone")
Case 1 of Lemma 5.4: if the verification identity
{uses "agm_verification_polynomial"}[] holds over the polynomial ring
for a fresh forgery message, the representation of `U*` is the zero
polynomial, so the forgery is invalid. Proved by power-separating
specialisation through the algebra map `spec`.
:::

:::proof "identity_case_lem54"
Eight coefficient read-offs. Each specialises the multivariate identity
through `spec` with a power-separating assignment, isolating one
coefficient of the forgery representation on a distinct power of `X`;
freshness of the forged message cancels the `(m* − mⱼ)` factors.
:::

:::theorem "sign_masks" (lean := "KVAC.Schemes.MicroCMZ.instSampleableNonVanishingMasks, KVAC.Schemes.MicroCMZ.reductionMaskSample, KVAC.Schemes.MicroCMZ.signMaskFun, KVAC.Schemes.MicroCMZ.signMaskFun_bijective, KVAC.Schemes.MicroCMZ.signMaskEquiv, KVAC.Schemes.MicroCMZ.sign_U_dist_eq, KVAC.Schemes.MicroCMZ.sign_masked_tag_dist_eq, KVAC.Schemes.MicroCMZ.sign_U_bu_dist_eq") (parent := "cmz_amac") (tags := "milestone")
Distributional lemmas for the sign oracle of {uses "mucmz_base_mac"}[]:
masks conditioned on a nonvanishing tag base, the shear bijection making
the mask coordinate perfectly hidden, and the identical-distribution
statements the reduction consumes.
:::

:::proof "sign_masks"
The shear map `(aᵤ, bᵤ) ↦ (Uⱼ, bᵤ)` is a bijection on the conditioned
mask space, so every fiber has equal size and the masked tag's
distribution matches the honest sign oracle's; the mask coordinate stays
uniform on every fiber.
:::

:::theorem "mucmz_mac_security" (parent := "cmz_amac") (tags := "paper, O24 Thm 5.1") (effort := "large") (priority := "high")
*O24 Theorem 5.1.* In the algebraic group model, μCMZ is an
`n`-attribute algebraic MAC ({uses "algebraic_mac"}[]), UF-CMVA secure in the
game of {uses "ufcmva_game"}[] under 3-DL and DL ({uses "hardness_assumptions"}[]), with
advantage at most `Adv^{3-dl} + Adv^{dl} + 3/p`.
:::

:::proof "mucmz_mac_security"
Factors through the single-attribute case {uses "single_attribute_mac"}[], lifted by
{uses "attribute_lifting"}[], with the two forgery cases bounded by
{uses "forgery_case_gap_dl"}[] and {uses "forgery_case_mac"}[].
:::

:::theorem "single_attribute_mac" (parent := "cmz_amac") (tags := "paper, O24 Lem 5.4") (effort := "large") (priority := "high")
*O24 Lemma 5.4.* Base case of {uses "mucmz_mac_security"}[]: in the algebraic group
model, single-attribute μCMZ is an algebraic MAC over `ℤ_p`, UF-CMVA
secure in the game of {uses "ufcmva_game"}[] under 3-DL ({uses "hardness_assumptions"}[]).
:::

:::proof "single_attribute_mac"
Played in the AGM game {uses "agm_model"}[]. Case split on the
adversary's algebraic representation of the forgery. If the
verification identity {uses "agm_verification_polynomial"}[] holds over
the polynomial ring, {uses "identity_case_lem54"}[] makes the forgery
invalid; otherwise the partial evaluation
{uses "partial_evaluation_psi"}[] embeds a 3-DL challenge whose discrete
logarithm is among at most 3 roots, with the challenge masked through
{uses "sign_masks"}[].
:::

:::theorem "attribute_lifting" (parent := "cmz_amac") (tags := "paper, O24 Lem 5.5") (effort := "medium") (priority := "medium")
*O24 Lemma 5.5.* Reduces `n`-attribute μCMZ security to the
single-attribute case {uses "single_attribute_mac"}[], giving its algebraic-MAC
advantage over `ℤ_p`.
:::

:::theorem "forgery_case_gap_dl" (parent := "cmz_amac") (tags := "paper, O24 Claim 5.6") (effort := "medium") (priority := "medium")
*O24 Claim 5.6.* In the μCMZ unforgeability proof, the first forgery
case is bounded by the gap discrete-log advantage ({uses "hardness_assumptions"}[]).
:::

:::theorem "forgery_case_mac" (parent := "cmz_amac") (tags := "paper, O24 Claim 5.7") (effort := "medium") (priority := "medium")
*O24 Claim 5.7.* In the μCMZ unforgeability proof, the second forgery
case is bounded by the single-attribute MAC's UF-CMVA advantage
({uses "ufcmva_game"}[]).
:::

:::definition "agm_verification_polynomial" (lean := "KVAC.Schemes.MicroCMZ.AGMPoly.Var, KVAC.Schemes.MicroCMZ.AGMPoly.instDecidableEqVar, KVAC.Schemes.MicroCMZ.AGMPoly.instFintypeVar, KVAC.Schemes.MicroCMZ.AGMPoly.P, KVAC.Schemes.MicroCMZ.AGMPoly.η, KVAC.Schemes.MicroCMZ.AGMPoly.x₀, KVAC.Schemes.MicroCMZ.AGMPoly.x₁, KVAC.Schemes.MicroCMZ.AGMPoly.xᵣ, KVAC.Schemes.MicroCMZ.AGMPoly.u, KVAC.Schemes.MicroCMZ.AGMPoly.keyPoly, KVAC.Schemes.MicroCMZ.AGMPoly.ReprCoeffs, KVAC.Schemes.MicroCMZ.AGMPoly.ReprCoeffs.toPoly, KVAC.Schemes.MicroCMZ.AGMPoly.ReprCoeffs.eval_toPoly, KVAC.Schemes.MicroCMZ.AGMPoly.eval_eq_zero_of_toPoly_eq_zero, KVAC.Schemes.MicroCMZ.AGMPoly.verifPoly, KVAC.Schemes.MicroCMZ.AGMPoly.verifPoly_eval, KVAC.Schemes.MicroCMZ.AGMPoly.verifPoly_eq_zero_iff, KVAC.Schemes.MicroCMZ.AGMPoly.totalDegree_keyPoly_le, KVAC.Schemes.MicroCMZ.AGMPoly.totalDegree_toPoly_le, KVAC.Schemes.MicroCMZ.AGMPoly.totalDegree_verifPoly_le") (parent := "cmz_amac") (tags := "paper, O24 Eq 12")
*O24 Equation 12.* The AGM verification polynomial identity for μCMZ
unforgeability at `n = 1`: a winning forgery against {uses "mucmz_construction"}[]
would force this identity in the secret exponents
`(η, x₀, xᵣ, x₁, u₁ … u_q)` over the polynomial ring.
:::

:::definition "partial_evaluation_psi" (lean := "KVAC.Schemes.MicroCMZ.AGMPoly.affineSubst, KVAC.Schemes.MicroCMZ.AGMPoly.eval_affineSubst, KVAC.Schemes.MicroCMZ.AGMPoly.natDegree_affineSubst_le") (parent := "cmz_amac") (tags := "paper, O24 Eq 16")
*O24 Equation 16.* The partial evaluation `ψ(χ)` of the verification
polynomial {uses "agm_verification_polynomial"}[]: collapsing the perfectly-hidden mask pairs
onto one fresh variable `χ` leaves a nonzero polynomial of degree at
most 3 that vanishes at the challenge's discrete logarithm. The affine
substitution and its degree bound are merged; the ≤3-roots bound
returns with the `AGMReduction` assembly.
:::

# Anonymity (Section 5.4)

:::group "cmz_anonymity"
μCMZ anonymity
:::

*Theorem 5.8.* μCMZ is anonymous (in the sense of *Framework*
anonymity) given a knowledge-sound ZK proof system. The
statistical-anonymity variant follows because μCMZ uses honest-verifier
zero-knowledge presentations with statistically indistinguishable
simulators.

*TODO (Track CMZ-A).* State and prove Theorem 5.8. Use the
`SampleableGroup` typeclass (the game-construction variant of the
prime-order-group typeclass).

:::theorem "mucmz_anonymity" (parent := "cmz_anonymity") (tags := "paper, O24 Thm 5.8") (effort := "large") (priority := "medium")
*O24 Theorem 5.8.* If ZKP proves the relation `R ⊇ R_cmz`
({uses "zk_arguments"}[]), then μCMZ ({uses "mucmz_construction"}[]) is anonymous in the
sense of {uses "kvac_anonymity"}[]: issuance and presentation are simulatable.
:::

# Extractability (Section 5.5)

:::group "cmz_extract"
μCMZ extractability
:::

*Theorem 5.2.* μCMZ is extractable (in the sense of *Framework*
extractability) in the algebraic group model. The proof uses
straight-line extraction from the *Proof systems* chapter plus Theorem
5.1.

*TODO (Track CMZ-E).* State and prove Theorem 5.2. The two key
ingredients are AGM straight-line extraction and the MAC unforgeability
result of Theorem 5.1.

:::theorem "mucmz_extractable_kvac" (parent := "cmz_extract") (tags := "paper, O24 Thm 5.2") (effort := "medium") (priority := "medium")
*O24 Theorem 5.2.* If ZKP proves the relation `R ⊇ R_cmz`
({uses "zk_arguments"}[]), then μCMZ ({uses "mucmz_construction"}[]) is an extractable
keyed-verification credential in the sense of {uses "kvac_extractability"}[].
:::

:::proof "mucmz_extractable_kvac"
Combines anonymity {uses "mucmz_anonymity"}[] and extractability
{uses "mucmz_extractability"}[].
:::

:::theorem "mucmz_extractability" (parent := "cmz_extract") (tags := "paper, O24 Thm 5.10") (effort := "large") (priority := "medium")
*O24 Theorem 5.10.* If ZKP proves `R ⊇ R_cmz` ({uses "zk_arguments"}[]), then
μCMZ is extractable ({uses "kvac_extractability"}[]) for the supported attribute
family.
:::

:::proof "mucmz_extractability"
The credential extractors wrap the proof system's extractors; the
reduction lands on MAC unforgeability {uses "mucmz_mac_security"}[], with the
candidate instance `Z` checked through the auxiliary Help oracle.
:::

# One-more unforgeability (Section 5.6)

:::group "cmz_omuf"
μCMZ one-more unforgeability
:::

*Theorem 5.3.* The anonymous-token variant `μCMZ_AT` is one-more
unforgeable in the algebraic group model under 2-DL. `μCMZ_AT` is the
zero-attribute specialisation of μCMZ, providing only an
anonymous-token binding.

*TODO (Track CMZ-OMUF).* State and prove Theorem 5.3 against the OMUF
game from the *Preliminaries* chapter.

:::theorem "mucmz_at_omuf" (parent := "cmz_omuf") (tags := "paper, O24 Thm 5.3") (effort := "large") (priority := "low")
*O24 Theorem 5.3.* If ZKP proves `R ⊇ R_cmz.p ∪ R_cmz.is`
({uses "zk_arguments"}[]), the variant `μCMZ_AT` of {uses "mucmz_construction"}[] is a
one-more unforgeable anonymous token ({uses "anonymous_tokens"}[]) in the game of
{uses "omuf_game"}[].
:::

:::proof "mucmz_at_omuf"
Reduces to the AGM one-more unforgeability bound {uses "mucmz_at_agm_omuf"}[].
:::

:::theorem "mucmz_at_agm_omuf" (parent := "cmz_omuf") (tags := "paper, O24 Thm 5.11") (effort := "large") (priority := "low")
*O24 Theorem 5.11.* In the algebraic group model, `μCMZ_AT` is a
one-more unforgeable anonymous token ({uses "omuf_game"}[]) for `n`
attributes.
:::

:::proof "mucmz_at_agm_omuf"
Case analysis over the adversary's `q + 1` forgeries, with the three
cases bounded by {uses "omuf_case_i"}[], {uses "omuf_case_ii"}[], and
{uses "omuf_case_iii"}[].
:::

:::theorem "omuf_case_i" (parent := "cmz_omuf") (tags := "paper, O24 Claim 5.12") (effort := "medium") (priority := "low")
*O24 Claim 5.12.* In the `μCMZ_AT` one-more unforgeability proof, case
(i) occurs with probability at most `q/p` plus the discrete-log
advantage ({uses "hardness_assumptions"}[]).
:::

:::theorem "omuf_case_ii" (parent := "cmz_omuf") (tags := "paper, O24 Claim 5.13") (effort := "medium") (priority := "low")
*O24 Claim 5.13.* In the `μCMZ_AT` one-more unforgeability proof, case
(ii) occurs with probability at most `1/p` plus the discrete-log
advantage ({uses "hardness_assumptions"}[]).
:::

:::theorem "omuf_case_iii" (parent := "cmz_omuf") (tags := "paper, O24 Claim 5.14") (effort := "medium") (priority := "low")
*O24 Claim 5.14.* In the `μCMZ_AT` one-more unforgeability proof, case
(iii) occurs with probability at most `3(1/p + Adv^{2-dl})`
({uses "hardness_assumptions"}[]).
:::
