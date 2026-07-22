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
value (the code) and the run's trace, that is, the output pair, the
random-oracle cache, and, for simulation extractability, the simulation log.
The optional crs trapdoor is omitted; the paper's instantiations never use it
(PR #54, `Extraction.lean`).

**Rejected alternative.** The standard black-box convention, where the
extractor has rewindable oracle access to the prover and sees neither its
coins nor its code. Tom Shrimpton advocated it during the review of the
security-model-agnostic specification (PR #34), before the paper-faithful
specification existed; it is not a comment on the extraction layer now
committed.

**Fidelity argument.** O24 defines the extractor over the coins and code of A,
and its §9 instantiation is inherently non-black-box, since it relies on AGM
representations. White-box access subsumes rewindable black-box access, since
the extractor can re-run the adversary value. Issue #43 records the
discussion; the paper-fidelity requirement decides it.

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

## Schwartz–Zippel bound `3/p`, not the paper's `1/p`

**Decision.** The Eq. 16 root bound for the non-identity case of Lemma 5.4 is
`3/p`. The degree tower gives `deg ψ ≤ totalDegree ϕ ≤ 3`
(`totalDegree_verifPoly_le`, `natDegree_affineSubst_le`), and a nonzero `ψ`
has at most 3 roots in `F` (`card_roots_affineSubst_verifPoly_le`), so the bad
event `ψ ≡ 0` over the uniform masks is bounded by `3/p`
(`AGMPolynomial.lean`, branch `microCMZ-agm-polynomial`). Unlike the other
entries, the rejected alternative here is the paper's own value, dropped on
correctness grounds rather than fidelity.

**Rejected alternative.** O24 Eq. 16 states the bound as `1/p`.

**Fidelity argument.** The paper invokes Schwartz–Zippel to bound `ψ ≡ 0`, and
for a degree-`d` polynomial that bound is `d/p`, not `1/p`. Writing
`ψ(χ) = ϕ(a + χ·b)`, the coefficient of `χ^d` in `ψ` (with `d = totalDegree ϕ
≤ 3`) is exactly `ϕ_d(b)`, the top-degree homogeneous part of `ϕ` evaluated at
the mask vector `b`: only the degree-`d` monomials of `ϕ` can reach `χ^d`, and
each contributes the product of its `b`-masks. Since `ϕ ≠ 0` we have `ϕ_d ≠ 0`,
so `ψ ≡ 0 ⟹ ϕ_d(b) = 0`, and Schwartz–Zippel on the nonzero degree-`d` form
`ϕ_d` in the uniform independent masks gives `Pr_b[ϕ_d(b) = 0] ≤ d/p ≤ 3/p`.
The `1/p` would be correct only for a degree-1 form; the degree-3 verification
polynomial needs `3/p`. The deviation loosens the concrete additive term
(`1/p → 3/p`) but leaves the asymptotic bound, and hence the security
statement, unchanged. The full derivation is documented at the head of the
Eq. 16 section in `AGMPolynomial.lean`.

## Open alternatives

None at present.
