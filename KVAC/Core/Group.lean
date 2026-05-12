/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Prime-order group

Abstract typeclass for the prime-order group `G` used throughout Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
(§3.1). All higher-layer modules (`Preliminaries/`, `ProofSystems/`,
`Framework/`, `Schemes/`) are stated over this typeclass rather than a specific
curve.

Concrete instances live under `KVAC/Instances/` and are added when the
`Examples/` track lands — Ristretto255 (via
[`curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify))
for the μCMZ instance.

## Notation convention

This formalisation uses **additive notation** throughout, matching O24 §3.1.
The paper's `xG = X` translates directly to Lean's `x • generator = X`. See
[`docs/STYLE_GUIDE.md`](../../docs/STYLE_GUIDE.md), section *Notation
conventions*, for the project-wide rule.

## Out of scope here

- Random-oracle interfaces (`H_p`, `H_G`) — formalised in `KVAC/Core/Hash.lean`.
- A formal adversary type (PPT, advantage, negligibility) — formalised in
  `KVAC/Instances/VCVioOracle.lean`. The hardness assumptions below are stated
  as `True` placeholders for now; they will be replaced once that file lands.
- Algebraic Group Model and Generic Group Model — these are proof-theoretic
  adversary models, not properties of the group itself.
-/

namespace KVAC.Core

/--
A prime-order group as used in O24 §3.1: a finite abelian group `G` of *odd*
prime order `p`, with a canonical generator.

The paper writes `Γ = (G, p, G)` where the first `G` is the carrier, `p` is the prime
order, and the second `G ∈ G` is the generator. Here those become the three fields
`(G, order, generator)` of the typeclass.

Use the additive scalar action `x • generator` (with `x : ℤ` or `x : ZMod
order`) to match the paper's `xG`.
-/
class PrimeOrderGroup (G : Type*) extends AddCommGroup G where
  /-- The prime order `p` of the group. -/
  order : ℕ
  /-- `order` is prime; declared as a `Fact` so Mathlib lemmas (e.g. the field
  structure of `ZMod order`) propagate via instance synthesis. -/
  [order_prime : Fact (Nat.Prime order)]
  /-- O24 specifies *odd* prime order, so `order ≠ 2`. -/
  order_odd : 2 < order
  /-- The cardinality of `G` matches `order`. -/
  card_eq : Nat.card G = order
  /-- The canonical generator. The paper denotes this `G ∈ G`. -/
  generator : G
  /-- `generator` generates `G`: integer scalar multiplication onto `G` is
  surjective. Implies `IsAddCyclic G` via the instance below. -/
  generator_zsmul_surjective : Function.Surjective (· • generator : ℤ → G)

attribute [instance] PrimeOrderGroup.order_prime

/-- A prime-order group is additive-cyclic. -/
instance PrimeOrderGroup.toIsAddCyclic (G : Type*) [inst : PrimeOrderGroup G] :
    IsAddCyclic G where
  exists_zsmul_surjective := ⟨inst.generator, inst.generator_zsmul_surjective⟩

/-! ## Cryptographic assumptions (O24 §3.1)

These are stated as `True` placeholders for now. The intended formal statements
quantify over PPT adversaries and bound the advantage as negligible in the
security parameter `λ`. Once `KVAC/Instances/VCVioOracle.lean` lands and
introduces the adversary type and the advantage / negligibility framework, each
`def` below should be replaced by the concrete game-based statement. Until
then, schemes can refer to these assumptions by name without committing to a
specific adversary model.
-/

/--
The discrete-logarithm (DL) assumption for `G` (O24 §3.1, ¶1).

> The discrete logarithm (DL) assumption holds for `GrGen` if it is
> computationally hard, given `X ←$ G` uniformly distributed, to compute
> `x ∈ ℤ_p` such that `xG = X`.

TODO: replace this placeholder with the concrete statement
`∀ PPT A, Adv^dl_{G,A}(λ)` is negligible in `λ`, once
`KVAC/Instances/VCVioOracle.lean` lands.
-/
def DLHard (G : Type*) [PrimeOrderGroup G] : Prop := True

/--
The decisional Diffie–Hellman (DDH) assumption for `G` (O24 §3.1, ¶1).

> The DDH assumption holds for `GrGen` if it is hard to distinguish the
> tuple `(P, aP, bP, abP)` from `(P, aP, bP, cP)` with `a, b, c ←$ ℤ_p` and
> `P ∈ G`.

TODO: replace this placeholder with the formal indistinguishability game,
once `KVAC/Instances/VCVioOracle.lean` lands.
-/
def DDHHard (G : Type*) [PrimeOrderGroup G] : Prop := True

/--
The gap discrete-logarithm assumption for `G` (O24 §3.1, ¶1).

> The gap discrete logarithm assumption holds if DL is hard even in the
> presence of a DDH oracle for the DL challenge.

A *stronger* assumption than `DLHard G`: the adversary additionally has
oracle access to DDH for the DL challenge tuple. Included for completeness;
neither μCMZ nor μBBS centrally depends on it in v1.

TODO: replace this placeholder with the formal statement, once
`KVAC/Instances/VCVioOracle.lean` lands.
-/
def GapDLHard (G : Type*) [PrimeOrderGroup G] : Prop := True

/--
The `q`-discrete-logarithm (`q`-DL) assumption for `G` (O24 §3.1, ¶2).

> The q-DL assumption holds for `GrGen` if it is hard for any PPT adversary
> to recover `x` uniformly distributed over `ℤ_p` given as input
> `(G, xG, x²G, …, x^q G)`.

μCMZ relies on the special case `q = 3`; μBBS relies on the general `q`-DL
with `q` polynomial in the security parameter.

TODO: replace this placeholder with the formal statement, once
`KVAC/Instances/VCVioOracle.lean` lands; at that point, `_q` will be renamed
back to `q` and used in the body.
-/
def QDLHard (_q : ℕ) (G : Type*) [PrimeOrderGroup G] : Prop := True

/--
The `3`-DL assumption used by μCMZ. Special case of `QDLHard 3 G`.
-/
abbrev ThreeDLHard (G : Type*) [PrimeOrderGroup G] : Prop := QDLHard 3 G

/--
The `q`-DDHI assumption for `G` (O24 §3.1, ¶2).

> The q-DDHI assumption holds for `GrGen` if it is hard for any PPT adversary
> to distinguish `(xG, x²G, …, x^q G, x⁻¹ G)` from `(xG, x²G, …, x^q G, Z)`
> for `x ←$ ℤ_p` and `Z ←$ G`.

TODO: replace this placeholder with the formal indistinguishability game, once
`KVAC/Instances/VCVioOracle.lean` lands; at that point, `_q` will be renamed
back to `q` and used in the body.
-/
def QDDHIHard (_q : ℕ) (G : Type*) [PrimeOrderGroup G] : Prop := True

end KVAC.Core
