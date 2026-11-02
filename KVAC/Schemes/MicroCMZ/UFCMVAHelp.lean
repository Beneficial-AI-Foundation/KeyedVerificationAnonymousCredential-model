/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Construction
import KVAC.Core.AlgebraicMAC.Security

/-!
# The UF-CMVA game of μCMZ with the oracle `Help` (O24 §5.2)

The unforgeability game of O24 Figure 5 for the base MAC of μCMZ, with the
oracle `Help(A₀, A⃗, Z)` of §5.2 (p. 35), which returns 1 if
`Z = (x₀ + xᵣ)•A₀ + Σᵢ xᵢ•Aᵢ` and 0 otherwise. The paper proves Theorem 5.1, in
the algebraic group model, for this game: "the scheme is unforgeable even if the
adversary is given one additional oracle Help". The proof of Theorem 5.10
(§5.5, p. 43) uses the answer of `Help` for its candidate `Z`.

The game is the honest one. The challenger holds the key and answers `Help` by
evaluating the equation, and no query carries an algebraic representation. The
AGM game `AGM_UF_CMVAGame` of `AlgebraicMAC.lean` is the device of the
proof of Lemma 5.4, where the reduction answers `Help` from the representations
of an algebraic adversary (p. 38). Among the MAC results, the paper assumes the
algebraic group model in Theorem 5.1 and Lemma 5.4 only.

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
and `verify` are those of O24 Figure 5, `help A₀ A⃗ Z` is the oracle of §5.2. -/
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

/-- The honest oracles of the game for the key `sk`. `sign` and `verify` are the
oracles `ufOracleImpl` of the plain game at μCMZ, and `help` evaluates `helpEq`
with the key. The state is the list of messages whose MAC codes the adversary
received. -/
noncomputable def ufHelpOracleImpl (secParam : ℕ) (H : G) (sk : Key F n) :
    QueryImpl (UFHelpOracleSpec F G n) (StateT (List (Fin n → F)) ProbComp)
  | .sign m => ufOracleImpl (μCMZBaseMACSyntax F gen) (secParam := secParam) H sk (.sign m)
  | .verify m σ =>
      ufOracleImpl (μCMZBaseMACSyntax F gen) (secParam := secParam) H sk (.verify m σ)
  | .help A₀ A Z => StateT.mk fun signed =>
      pure (helpEq sk A₀ A Z, signed)

/-! ## The game -/

/-- An adversary of the UF-CMVA game with `Help` for μCMZ with `n` attributes.
Given the crs `H` and the public parameters `(X₀, Xᵣ, X⃗)`, it queries the three
oracles and outputs a forgery `(m⃗*, (U*, V*))`. It has a private coin oracle
`unifSpec` beside the game's oracles, as the one-more forgers do, so that a
reduction built from a sampling adversary, such as the `B` of Theorem 5.10, is
one inhabitant of this type. -/
structure UFHelpAdversary (F G : Type) (n : ℕ) where
  /-- The adversary's program, from the crs and the public parameters. -/
  run : G → Params G n →
    OracleComp (unifSpec + UFHelpOracleSpec F G n) ((Fin n → F) × Code G)

/-- The UF-CMVA game with `Help` for μCMZ, O24 Figure 5 with the oracle of §5.2.
Setup and key generation are those of `μCMZBaseMACSyntax`. The private coin
oracle is answered in `ProbComp`. The adversary wins when its forged message is
fresh and its forgery verifies, as in `UF_CMVAGame`. -/
noncomputable def UF_CMVAHelpGame (secParam : ℕ) (A : UFHelpAdversary F G n) :
    ProbComp Bool := do
  let mac := μCMZBaseMACSyntax F gen
  let H : G ← mac.setup secParam n
  let (sk, pp) ← (mac.keygen (secParam := secParam) (n := n) H :
      ProbComp (Key F n × Params G n))
  -- `HAdd.hAdd` rather than `+`, since the instance search for `+` times out in
  -- the instance context of this file.
  let impl := HAdd.hAdd
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List (Fin n → F)) ProbComp))
    (ufHelpOracleImpl gen secParam H sk)
  let ((mStar, σStar), signed) ← (simulateQ impl (A.run H pp)).run []
  pure (decide (mStar ∉ signed) && mac.verify (secParam := secParam) H sk mStar σStar)

/-- The advantage in the UF-CMVA game with `Help`, the probability that
`UF_CMVAHelpGame` returns `true`. The paper's `Adv^ufcmva_μCMZ` is the advantage
in Figure 5, without `Help`. Theorem 5.1 (p. 35) bounds the advantage with `Help`
as well, in the algebraic group model, and the proof of Theorem 5.10 (p. 43)
uses the game with `Help`. -/
noncomputable abbrev UF_CMVAHelpAdv (A : UFHelpAdversary F G n) (secParam : ℕ) : ℝ≥0∞ :=
  Pr[= true | UF_CMVAHelpGame gen secParam A]

/-! ## The game without `Help`

An adversary of the generic `UF_CMVAGame` at μCMZ never queries `Help`. It is
an adversary of this game with the same advantage, so a bound on this game over
all adversaries covers the plain game of Figure 5. -/

/-- The queries of the plain game as queries of the game with `Help`, on the
game's side of the coin oracle. -/
def ufQueryToHelp {secParam : ℕ} (H : G) :
    QueryImpl (UFOracleSpec (μCMZBaseMACSyntax F gen) (secParam := secParam) (n := n) H)
      (OracleComp (unifSpec + UFHelpOracleSpec F G n))
  | .sign m => query (spec := unifSpec + UFHelpOracleSpec F G n) (.inr (.sign m))
  | .verify m σ => query (spec := unifSpec + UFHelpOracleSpec F G n) (.inr (.verify m σ))

/-- An adversary of the plain game at μCMZ as an adversary of the game with
`Help`, which never queries `Help` and never draws a coin. -/
def ufAdversaryToHelp (A : UFAdversary (μCMZBaseMACSyntax F gen))
    (secParam : ℕ) : UFHelpAdversary F G n where
  run H pp :=
    simulateQ (ufQueryToHelp gen (secParam := secParam) H)
      (A.run (secParam := secParam) (n := n) H pp)

/-- The embedding preserves the advantage. Setup and key generation are shared, and
the oracles of the game with `Help`, composed with `ufQueryToHelp`, are those of the
plain game query by query. -/
theorem UF_CMVAHelpAdv_ufAdversaryToHelp (A : UFAdversary (μCMZBaseMACSyntax F gen))
    (secParam : ℕ) :
    UF_CMVAHelpAdv gen (ufAdversaryToHelp gen A secParam (n := n)) secParam =
      UF_CMVAAdv (μCMZBaseMACSyntax F gen) A secParam n := by
  refine congrArg (Pr[= true | ·]) ?_
  simp only [UF_CMVAHelpGame, UF_CMVAGame, ufAdversaryToHelp, ← QueryImpl.simulateQ_compose]
  refine bind_congr fun H => bind_congr fun keys => ?_
  congr 3
  funext q
  cases q <;> exact simulateQ_spec_query ..

end KVAC.Schemes.MicroCMZ
