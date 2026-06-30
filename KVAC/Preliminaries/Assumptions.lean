/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.Group
import VCVio

/-!
# Cryptographic hardness assumptions (O24 §3.1)

The q-power discrete logarithm (q-DL) and gap discrete logarithm (gap-DL)
experiments from Orrù, *Revisiting Keyed-Verification Anonymous Credentials*,
IACR ePrint 2024/1552, §3.1. DL / CDH / DDH already exist upstream in VCVio
(`VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`); this file
adds the two assumptions O24 needs that VCVio does not provide.

- **q-DL**: the adversary receives `(G₀, x·G₀, x²·G₀, …, x^q·G₀)` and must
  output `x`. μCMZ's MAC unforgeability reduces to 3-DL (O24 Theorem 5.1), the
  anonymous-token variant μCMZ_AT to 2-DL (Theorem 5.3), and μBBS to (q+2)-DL.
- **gap-DL**: DL where the adversary may additionally query a DDH-decision
  oracle relative to the challenge, `Ddh(A, Z) = 1 ↔ Z = x·A`. Used in the
  n-to-1 attribute reduction of O24 Lemma 5.5 (Claim 5.6).

O24 §3.1 also states a q-DDHI assumption, needed for μBBS/HashDY,
deferred together with μBBS; we therefore defer formalizing q-DDHI to future work.

## Conventions

Experiments are `ProbComp Bool` in the style of VCVio's `dlogExp`; advantages
are `ℝ≥0∞` via `Pr[= true | ·]`, matching `KVAC.Core.UF_CMVAAdv`. The gap-DL
adversary is an `OracleComp` over `unifSpec + GapDLogOracleSpec G` — the left arm
provides uniform sampling, the right arm the DDH-decision oracle — simulated
with `QueryImpl.ofLift` / `simulateQ` as in VCVio's `FiatShamir`.

This is a game-construction file, so it uses the `SampleableGroup` binder block
(see `docs/STYLE_GUIDE.md`, *Prime-order group convention*).
-/

set_option autoImplicit false

namespace KVAC.Preliminaries

open KVAC.Core OracleComp OracleSpec ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

/-! ## q-DL (q-power discrete logarithm) -/

/-- A q-DL adversary: receives the generator `g` and the q powers
`(x·g, x²·g, …, x^q·g)`, and tries to output the exponent `x`. -/
def QDLogAdversary (q : ℕ) (F G : Type) := G → (Fin q → G) → ProbComp F

/-- q-DL experiment (O24 §3.1): sample `x ←$ F`, give the adversary `g` and
`i ↦ x^(i+1) · g` for `i ∈ [q]`, and check whether its output equals `x`.
For `q = 1` this coincides with the standard DL experiment. -/
def qdlogExp (q : ℕ) (g : G) (adversary : QDLogAdversary q F G) : ProbComp Bool := do
  let x ← $ᵗ F
  let x' ← adversary g (fun i => (x ^ ((i : ℕ) + 1)) • g)
  return decide (x' = x)

/-- The q-DL advantage of an adversary, as `Pr[= true | qdlogExp …]`. -/
noncomputable abbrev qdlogAdv (q : ℕ) (g : G) (adversary : QDLogAdversary q F G) : ℝ≥0∞ :=
  Pr[= true | qdlogExp q g adversary]

/-- The 3-DL advantage (O24 Theorem 5.1's assumption for μCMZ). -/
noncomputable abbrev threeDlogAdv (g : G) (adversary : QDLogAdversary 3 F G) : ℝ≥0∞ :=
  qdlogAdv 3 g adversary

/-- The 2-DL advantage (O24 Theorem 5.3's assumption for μCMZ_AT). -/
noncomputable abbrev twoDlogAdv (g : G) (adversary : QDLogAdversary 2 F G) : ℝ≥0∞ :=
  qdlogAdv 2 g adversary

/-- VCVio's DL experiment in the project's `ℝ≥0∞` advantage convention. -/
noncomputable abbrev dlogAdv (g : G) (adversary : DiffieHellman.DLogAdversary F G) : ℝ≥0∞ :=
  Pr[= true | DiffieHellman.dlogExp g adversary]

/-! ## gap-DL (discrete logarithm with a DDH-decision oracle) -/

/-- The oracle interface for gap-DL: a single oracle taking pairs `(A, Z)` and
answering a Boolean — honestly, whether `Z = x·A` for the challenge exponent
`x` (the "DH of the challenge `X = x·g` and `A`"). -/
abbrev GapDLogOracleSpec (G : Type) : OracleSpec (G × G) := (G × G) →ₒ Bool

/-- A gap-DL adversary: receives `(g, x·g)`; may sample uniformly (left oracle
arm) and query the DDH-decision oracle (right arm); tries to output `x`. -/
def GapDLogAdversary (F G : Type) :=
  G → G → OracleComp (unifSpec + GapDLogOracleSpec G) F

/-- Honest implementation of the gap-DL DDH-decision oracle for challenge
exponent `x`: answer `(A, Z)` with `Z = x·A`. -/
def gapDdhOracleImpl (x : F) : QueryImpl (GapDLogOracleSpec G) ProbComp :=
  fun q => pure (decide (q.2 = x • q.1))

/-- gap-DL experiment: sample `x ←$ F`, run the adversary on `(g, x·g)` with
uniform sampling passed through and DDH-decision queries answered by
`gapDdhOracleImpl x`, and check whether its output equals `x`. -/
def gapDlogExp (g : G) (adversary : GapDLogAdversary F G) : ProbComp Bool := do
  let x ← $ᵗ F
  let x' ← simulateQ (QueryImpl.ofLift unifSpec ProbComp + gapDdhOracleImpl x)
    (adversary g (x • g))
  return decide (x' = x)

/-- The gap-DL advantage of an adversary, as `Pr[= true | gapDlogExp …]`. -/
noncomputable abbrev gapDlogAdv (g : G) (adversary : GapDLogAdversary F G) : ℝ≥0∞ :=
  Pr[= true | gapDlogExp g adversary]

end KVAC.Preliminaries
