/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim, Semar Augusto
-/

/-!
# Keyed setup — the shared CRS and key-generation skeleton

The algebraic MAC (`KVAC.Core.AlgebraicMAC`, O24 Definition 3.1) and the
keyed-verification credential system (`KVAC.Framework`, O24 Definition 4.2)
begin the same way: sample a CRS `crs ← S(1^λ, n)`, then a key pair
`(sk, pp) ← K(crs)` over a fixed message space. `KeyedSetupSyntax` bundles that
shared preamble; each primitive `extends` it and adds only its own operations.

A Lean-level factoring, not an O24 object — the paper states Def 3.1 and Def 4.2
separately. Sharing the carriers and generation algorithms means the intrinsic-
typing discipline is described once, while `AlgebraicMACSyntax` and `KVACSyntax`
stay verbatim against their definitions.

## Intrinsic typing

`Crs : Nat → Nat → Type` makes the CRS depend on both the security parameter and
the attribute count; the carriers `Msg`, `Sk`, `Pp` then depend on a specific
CRS value, so the type-checker enforces arity agreement across a scheme's
algorithms. The structure is polymorphic in the randomness monad `M`, so a
value can be read deterministically (`Id`), probabilistically (`ProbComp`), or
symbolically.
-/

namespace KVAC.Core

/--
The shared setup of a keyed scheme in the CRS model: a common reference string,
a message space, and a key pair, with the algorithms that sample them. Extended
by the algebraic MAC (Def 3.1) and the credential system (Def 4.2).
-/
structure KeyedSetupSyntax (M : Type → Type) [Monad M] where
  /-- CRS type, indexed by the security parameter and attribute count. -/
  Crs : Nat → Nat → Type
  /-- Message (attribute) type, selected by the CRS; schemes operate on
  vectors `Fin n → Msg crs`. -/
  Msg : {secParam n : Nat} → Crs secParam n → Type
  /-- Decidable equality on messages, needed by the security games' freshness
  checks. As a field it does mildly constrain instantiators to decidable
  message spaces — benign in practice, since the concrete schemes use finite
  fields and groups. -/
  DecidableEqMsg : {secParam n : Nat} → (crs : Crs secParam n) →
    DecidableEq (Msg crs)
  /-- Secret-key type, selected by the CRS. -/
  Sk : {secParam n : Nat} → Crs secParam n → Type
  /-- Public-parameter type, selected by the CRS. -/
  Pp : {secParam n : Nat} → Crs secParam n → Type
  /-- Setup: `crs ← S(1^λ, n)`. -/
  setup : (secParam n : Nat) → M (Crs secParam n)
  /-- Key generation: `(sk, pp) ← K(crs)`. -/
  keygen : {secParam n : Nat} → (crs : Crs secParam n) → M (Sk crs × Pp crs)

namespace KeyedSetupSyntax

variable {M : Type → Type} [Monad M] (ks : KeyedSetupSyntax M)
variable {secParam n : Nat}

/-- `DecidableEqMsg` promoted to an instance; inherited by every `extends`. -/
instance (crs : ks.Crs secParam n) : DecidableEq (ks.Msg crs) :=
  ks.DecidableEqMsg crs

/-- An `n`-attribute vector under the CRS (the paper's `m⃗ ∈ M^n`). -/
abbrev MsgVec (crs : ks.Crs secParam n) : Type := Fin n → ks.Msg crs

end KeyedSetupSyntax

/--
The three-move issuance plumbing shared by every keyed scheme with blind
issuance: the user's first move yields private state and a request, the
server answers the request or rejects (`none`), and the user finalizes from
its state and the response, or aborts (`none`). `KVACSyntax.issue`
(O24 Definition 4.2) and `ATSyntax.issue` (O24 §3.4) are both instances;
`none` propagates either party's failure.
-/
def issueChain {M : Type → Type} [Monad M] {St Req Resp Out : Type}
    (usr₁ : M (St × Req)) (srv : Req → M (Option Resp))
    (usr₂ : St → Resp → M (Option Out)) : M (Option Out) := do
  let (st, μ) ← usr₁
  match ← srv μ with
  | none => pure none
  | some resp => usr₂ st resp

end KVAC.Core
