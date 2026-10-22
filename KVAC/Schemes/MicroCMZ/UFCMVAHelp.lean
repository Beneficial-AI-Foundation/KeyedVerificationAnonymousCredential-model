/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Construction
import KVAC.Core.AlgebraicMAC.Security

/-!
# The UF-CMVA game of μCMZ with the oracle `Help` (O24 §5.3)

The unforgeability game of O24 Figure 5 for the base MAC of μCMZ, with the
oracle `Help` of §5.3. Theorem 5.1 (p. 35) is proved for this game, "we actually
will prove a stronger claim: the scheme is unforgeable even if the adversary is
given one additional oracle `Help(A₀, A⃗, Z)` that returns 1 if `Z = (x₀ +
xᵣ)•A₀ + Σᵢ xᵢ•Aᵢ` and 0 otherwise". The reduction of Theorem 5.10 (§5.5, p. 43)
checks its candidate `Z` through `Help`.

The game is the honest one. The challenger holds the key and answers `Help` by
evaluating the equation, and no query carries an algebraic representation. The
instrumented game `AGM_UF_CMVAGame` of `AlgebraicMAC.lean` is the device of the
proof of Lemma 5.4, where the reduction answers `Help` from the representations
of an algebraic adversary (p. 38). The paper states the algebraic group model as
a hypothesis of Theorem 5.1 and of Lemma 5.4 only. The statement of Theorem
5.1 in `UFCMVA.lean`, `microCMZ_ufcmva_le_of_wellBehaved`, bounds the plain game
of Figure 5 for well-behaved algebraic adversaries. Their translation to the
plain game (`AGMBridge.lean`) answers `help` by `false`, and `WellBehaved`
forbids `Help` queries. A bound of Theorem 5.1 for this game, with `Help`
answered by the key, is open. Issue #235 proposes a transfer lemma onto it.

`Help` is specific to μCMZ, since its equation reads the key `(x₀, xᵣ, x⃗)`,
so the game is stated for `μCMZBaseMACSyntax` and not for the generic
`UF_CMVAGame` of `Core/AlgebraicMAC/Security.lean`. An adversary of that
generic game at μCMZ is an adversary of this game that never queries `Help`,
`ufAdversaryToHelp`, with the same advantage.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core ENNReal

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}
variable (gen : G)

/-! ## The oracles -/

/-- The oracle calls of the UF-CMVA game with `Help`, for `n` attributes. `sign`
and `verify` are those of O24 Figure 5, `help A₀ A⃗ Z` is the oracle of §5.3. -/
inductive UFHelpQuery (F G : Type) (n : ℕ) : Type where
  /-- `Sign(m⃗)`, a MAC code on `m⃗`. -/
  | sign : (Fin n → F) → UFHelpQuery F G n
  /-- `Verify(m⃗, σ)`, the verification bit. -/
  | verify : (Fin n → F) → Code G → UFHelpQuery F G n
  /-- `Help(A₀, A⃗, Z)`, whether `Z = (x₀ + xᵣ)•A₀ + Σᵢ xᵢ•Aᵢ`. -/
  | help : G → (Fin n → G) → G → UFHelpQuery F G n

/-- Answer types of `UFHelpQuery`, a MAC code for `sign`, a Boolean for
`verify` and `help`. -/
def UFHelpOracleSpec (F G : Type) (n : ℕ) : OracleSpec (UFHelpQuery F G n)
  | .sign _ => Code G
  | .verify _ _ => Bool
  | .help _ _ _ => Bool

/-- The equation of `Help`, `Z = (x₀ + xᵣ)•A₀ + Σᵢ xᵢ•Aᵢ` (O24 §5.3, p. 35). -/
def helpEq (sk : Key F n) (A₀ : G) (A : Fin n → G) (Z : G) : Bool :=
  decide (Z = (sk.1 + sk.2.1) • A₀ + ∑ i, sk.2.2 i • A i)

/-- The honest oracles of the game for the key `sk`. `sign` runs the MAC code
generation and records the message, `verify` runs the verification, and `help`
evaluates `helpEq` with the key. The state is the list of messages whose MAC
codes the adversary received, as `ufOracleImpl` keeps it. -/
noncomputable def ufHelpOracleImpl (secParam : ℕ) (H : G) (sk : Key F n) :
    QueryImpl (UFHelpOracleSpec F G n) (StateT (List (Fin n → F)) ProbComp)
  | .sign m => StateT.mk fun signed => do
      let σ : Code G ← (μCMZBaseMACSyntax F gen).MAC (secParam := secParam) H sk m
      pure (σ, m :: signed)
  | .verify m σ => StateT.mk fun signed =>
      pure ((μCMZBaseMACSyntax F gen).verify (secParam := secParam) H sk m σ, signed)
  | .help A₀ A Z => StateT.mk fun signed =>
      pure (helpEq sk A₀ A Z, signed)

/-! ## The game -/

/-- An adversary of the UF-CMVA game with `Help` for μCMZ with `n` attributes.
Given the crs `H` and the public parameters `(X₀, Xᵣ, X⃗)`, it queries the three
oracles and outputs a forgery `(m⃗*, (U*, V*))`. -/
structure UFHelpAdversary (F G : Type) (n : ℕ) where
  /-- The adversary's program, from the crs and the public parameters. -/
  run : G → Params G n → OracleComp (UFHelpOracleSpec F G n) ((Fin n → F) × Code G)

/-- The UF-CMVA game with `Help` for μCMZ, O24 Figure 5 with the oracle of §5.3.
Setup and key generation are those of `μCMZBaseMACSyntax`. The adversary wins
when its forged message is fresh and its forgery verifies, as in `UF_CMVAGame`. -/
noncomputable def UF_CMVAHelpGame (secParam : ℕ) (A : UFHelpAdversary F G n) :
    ProbComp Bool := do
  let mac := μCMZBaseMACSyntax F gen
  let H : G ← mac.setup secParam n
  let (sk, pp) ← (mac.keygen (secParam := secParam) (n := n) H :
      ProbComp (Key F n × Params G n))
  let ((mStar, σStar), signed) ←
    (simulateQ (ufHelpOracleImpl gen secParam H sk) (A.run H pp)).run []
  pure (decide (mStar ∉ signed) && mac.verify (secParam := secParam) H sk mStar σStar)

/-- The advantage in the UF-CMVA game with `Help`, the probability that
`UF_CMVAHelpGame` returns `true`. This is the `Adv^ufcmva_μCMZ` of O24
Theorem 5.1 (p. 35) and of the bound of Theorem 5.10 (p. 42). -/
noncomputable abbrev UF_CMVAHelpAdv (A : UFHelpAdversary F G n) (secParam : ℕ) : ℝ≥0∞ :=
  Pr[= true | UF_CMVAHelpGame gen secParam A]

/-! ## The game without `Help`

An adversary of the generic `UF_CMVAGame` at μCMZ never queries `Help`. It is
an adversary of this game with the same advantage, so the bound of
Theorem 5.1 for this game covers the plain game of Figure 5. -/

/-- The queries of the plain game as queries of the game with `Help`. -/
def ufQueryToHelp {secParam : ℕ} (H : G) :
    QueryImpl (UFOracleSpec (μCMZBaseMACSyntax F gen) (secParam := secParam) (n := n) H)
      (OracleComp (UFHelpOracleSpec F G n))
  | .sign m => query (spec := UFHelpOracleSpec F G n) (.sign m)
  | .verify m σ => query (spec := UFHelpOracleSpec F G n) (.verify m σ)

/-- An adversary of the plain game at μCMZ as an adversary of the game with
`Help`, which never queries `Help`. -/
noncomputable def ufAdversaryToHelp (A : UFAdversary (μCMZBaseMACSyntax F gen))
    (secParam : ℕ) : UFHelpAdversary F G n where
  run H pp :=
    simulateQ (ufQueryToHelp gen (secParam := secParam) H)
      (A.run (secParam := secParam) (n := n) H pp)

/-- The embedding preserves the advantage. The proof is deferred. -/
theorem UF_CMVAHelpAdv_ufAdversaryToHelp (A : UFAdversary (μCMZBaseMACSyntax F gen))
    (secParam : ℕ) :
    UF_CMVAHelpAdv gen (ufAdversaryToHelp gen A secParam (n := n)) secParam =
      UF_CMVAAdv (μCMZBaseMACSyntax F gen) A secParam n := by
  sorry

end KVAC.Schemes.MicroCMZ
