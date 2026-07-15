# Design alternatives

This document records formalization design decisions where an alternative was
rejected for fidelity with respect to the paper (Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint
[2024/1552](https://eprint.iacr.org/2024/1552), cited as O24). Closed decisions
live here. An alternative that still awaits a decision gets an issue; once
resolved, its outcome is summarized here and the issue is closed.

Each entry states the decision, the rejected alternative, the fidelity
argument, and where the decision landed.

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

## Open alternatives

- White-box versus black-box knowledge-soundness extractor, issue #43. O24
  §3.3 defines the extractor over the coins and code of the adversary
  (white-box); Tom Shrimpton advocates black-box rewindable access. The
  formalization follows O24. Confirmation is pending on whether black-box
  access is a hard constraint for the μCMZ instantiations.
