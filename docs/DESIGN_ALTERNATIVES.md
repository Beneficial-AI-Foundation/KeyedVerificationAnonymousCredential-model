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
coins nor its code. Tom Shrimpton advocates it.

**Fidelity argument.** O24 defines the extractor over the coins and code of A,
and its §9 instantiation is inherently non-black-box, since it relies on AGM
representations. White-box access subsumes rewindable black-box access, since
the extractor can re-run the adversary value. Issue #43 records the
discussion; the paper-fidelity requirement decides it.

## Open alternatives

None at present.
