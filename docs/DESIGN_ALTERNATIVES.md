# Design alternatives

This document records formalization design decisions where an alternative was
rejected for fidelity with respect to the paper (Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint
[2024/1552](https://eprint.iacr.org/2024/1552), cited as O24). Closed decisions
live here. An alternative that still awaits a decision gets an issue; once
resolved, its outcome is summarized here and the issue is closed.

Each entry states the decision, the rejected alternative, the fidelity
argument, and where the decision landed.

## Security-model-agnostic specification set aside

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

## Extractor and simulator exhibited existentially

**Decision.** The knowledge-soundness extractor and the zero-knowledge
simulator are exhibited in the security statements, not fields of the scheme
or of a security model (PR #34 introduced this; the paper-faithful
specification keeps it).

**Rejected alternative.** Extraction as a `SecurityModel` attribute
(`SecurityModel.extracts`) read by the properties.

**Fidelity argument.** In O24 §3.3 and in the standard definitions the
extractor is external to the game and to the scheme description. Tom Shrimpton
raised the point; issue #43 records it as resolved.

## Monadic verifier

**Decision.** `NIZKPSyntax.verify` returns `M Bool` (PR #45,
`Construction.lean`).

**Rejected alternative.** A deterministic verifier returning `Bool`, like
`MAC.V` of O24 §3.2.

**Fidelity argument.** O24 writes 0/1 ← ZKP.V with a sampling arrow, unlike
the deterministic 0/1 := MAC.V of §3.2, and a Fiat–Shamir verifier recomputes
c = H(a, x) through the random oracle, so the verifier must be effectful.

## Proveᵦ guard, oracle-side check with an `Option` answer

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

## Relation decidability scoped to the game

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

## White-box knowledge-soundness extractor

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

## NIZKP procedure carrier and the `verify` effect

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

## Conditioned sign masks.

**Decision.** The reduction's sign masks are sampled conditioned on Uⱼ ≠ 0 
(`SignMask.lean`, PR #48), giving exact coupling with the real oracle.

**Rejected alternative.** The paper's unrestricted `a_{u,j}, b_{u,j} ←$ ℤ_p` (Eq. 14).

**Fidelity argument.** The real experiment's U is uniform over `𝔾^×` and never zero, 
so Eq. 14's "identically distributed" holds only under the conditioning. 
The `(Uⱼ, bᵤ)` joint law stays independent uniform (`sign_U_bu_dist_eq`), 
so the masks' hiding is unaffected.
## Structured hash domains

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

## Exact-attribute predicate as a family field

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

## Schwartz–Zippel bound `3/p`, not the paper's `1/p`

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

## Eq. 13: X₀'s `X`-coefficient (O24 p. 37)

**Decision.** The challenge embedding builds `X₀`'s `X`-coefficient as
`a₀·b_h + b₀·a_h` (`AGMReduction/Core.lean`, PR #88, the Eq. 13 block of
`microCMZ3DLReduction`). Like the `3/p` entry above, the rejected alternative
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

## Eq. 14: the simulated signing response (O24 p. 37)

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

## The μCMZ_AT core removes both issuance proofs, not only the boxed π_iu

**Decision.** The formalized anonymous-token scheme is the *core* with both
issuance proofs removed, and is named accordingly (`μCMZATCore`,
`ATVariant.lean`). The `π_is`-carrying variant, together with a lifting lemma
bounding its one-more unforgeability by the core's plus one zero-knowledge
term for `ZKP_cmz.is`, is deferred until the upstream erratum settles; the
printed Theorem 5.3 blueprint node stays an unanchored stub meanwhile.

**Rejected alternatives.** (i) Formalizing the printed variant, which keeps
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

## Nonzero issuance nonces `u, r ←$ ℤ_p^×` where Figure 9 prints `ℤ_p`

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

## Anonymity game at fixed setup, negligibility over instance families

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
5.8 statement must bridge the two formulations. Recorded in
`docs/MICROCMZ_ANONYMITY_PLAN.md`.

## The issuer adversary runs before and after the user's request

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
oracle computation. Found in the codex review of the module.

## Two adversary structures, not one pair

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

## The anonymity simulator runs in the random-oracle state monad

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

## The Present oracle answers under the queried predicate

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
as a typo for φ′. Not yet reported to the author.

## Exact-length representations in the AGM OMUF game

**Decision.** In the AGM-instrumented one-more unforgeability game for the
μCMZ_AT core (`AGMOneMoreUnforgeability.lean`) a submitted representation is
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

## Open alternatives

**The crs and the group.** In the paper `μCMZ.S(1^λ, n)` runs `GrGen(1^λ)`
and returns `crs := (Γ, H)`, the group description together with a random
group element (Figure 8). The μCMZ instance fixes the group and its generator
as type parameters and returns only `H` from `setup`, so the framework's
quantifier "crs ∈ [KVAC.S(1^λ, n)]" ranges over every group of the class and
every `H`, with no λ in it. The faithful crs is `Γ × 𝔾`. Issue #148 tracks the
encodings, a deterministic family `GrGen : ℕ → Type` as the committed step,
and sampled group descriptions as the fully faithful one. Until it closes the
asymptotic predicates `Anonymous`, `AnonymousPoly`, `Extractable` and
`ExtractablePoly` are not provable for μCMZ, and the theorems bound the
advantages at fixed parameters.
