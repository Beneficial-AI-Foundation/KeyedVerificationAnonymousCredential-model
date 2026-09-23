/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game

/-!
# μCMZ_AT one-more unforgeability — the game transcript (O24 §5.6)

The run of the AGM-instrumented game of `Game.lean` as a record, for the
Theorem 5.11 proof at `n = 1`: `OMUFTrace` holds everything a run produces
before its decision, `agmOMUFTrace` is the run with the decision left out, and
`AGM_OMUFGame_eq_trace` says the game is the trace followed by the decision.
Track CMZ-OMUF, step A3 of the Theorem 5.3 plan, part 17a of item 17 (issue
#189).

The paper never names this object. Its proof speaks of "the execution": the
Sign queries `C_j` with their representations `γ⃗^(j)` (Equation 17), the
forgeries with `α⃗^(i), β⃗^(i)` (Equation 19), the logarithms `η, x₀, xᵣ, x₁, u_j`
the polynomials are evaluated at, and the Claims bound the probability that
"item (i) happens" over one such execution. A Claim stated in Lean needs a
computation whose outcome the event is a predicate on, and that outcome has to
carry the key and the representations. `OMUFTrace` is that outcome, on the
pattern of `RedTrace` in `AGMReduction/Core.lean`.

## What is defined, and what uses it

  agmOMUFTrace gen secParam A : ProbComp (OMUFTrace F G)   the run, decision left out
    |     AGM_OMUFGame_eq_trace     the game is the trace followed by the decision   (proved)
    '---> t : OMUFTrace F G   (sk, H, pp, log, out)

`CaseEvents.lean` reads the polynomials of Equations 18 and 22 off a trace and
defines the win and the three case events, items (i) to (iii) of p. 45, that
Claims 5.12 to 5.14 bound in `Statements.lean`. Through the equality lemma, the
game's success probability is the trace probability of the win, so bounds on
events that together cover the win bound the game.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

section Trace

variable (gen : G) (secParam : ℕ)

/--
Everything a run of `AGM_OMUFGame` produces before its decision: the key, the
crs, the public parameters, the final transcript, and the adversary's
forgeries with their representations. The Claims 5.12 to 5.14 are statements
about events of this trace; `AGM_OMUFGame_eq_trace` ties it to the game.
-/
structure OMUFTrace (F G : Type) where
  /-- The secret key `(x₀, xᵣ, x₁)`. -/
  sk : Key F 1
  /-- The crs `H`. -/
  H : G
  /-- The public parameters `(X₀, Xᵣ, X₁)`. -/
  pp : Params G 1
  /-- The final transcript of the Sign oracle. -/
  log : AGMOMUFLog F G 1
  /-- The forgeries with their representations (O24 Equation 19). -/
  out : List (AGMOMUFForgery F G 1)

/--
The run of `AGM_OMUFGame` at `n = 1` with the decision left out, in the shape of
`AGMReduction/Core.lean`'s `redTrace`: the same setup, key generation and
simulated adversary, returning the trace instead of the Boolean.
-/
noncomputable def agmOMUFTrace (A : AGMOMUFAdversary F G 1) : ProbComp (OMUFTrace F G) := do
  let tok := μCMZATCoreSyntax F gen
  let H : G ← tok.setup secParam 1
  let (sk, pp) ← tok.keygen (secParam := secParam) (n := 1) H
  let (out, log) ←
    (simulateQ (agmOMUFOracleImpl gen secParam sk H pp) (A.run H pp)).run []
  pure ⟨sk, H, pp, log, out⟩

/-- The game is the trace followed by the decision, so the game's success
probability is the trace probability of the win (`CaseEvents.lean`'s
`OMUFTrace.Wins`), and bounds on events that together cover the win bound the
game. -/
theorem AGM_OMUFGame_eq_trace (A : AGMOMUFAdversary F G 1) :
    AGM_OMUFGame gen secParam A =
      (agmOMUFTrace gen secParam A >>= fun t =>
        pure (decide (AGMOMUFWins gen secParam t.sk t.H t.pp t.log t.out))) := by
  -- After reassociating, the sides differ only by a `pure x >>= f` redex at the leaf,
  -- which `OracleComp`'s bind reduces definitionally; any drift between the game and
  -- the trace breaks this proof.
  unfold AGM_OMUFGame agmOMUFTrace
  simp only [bind_assoc]
  congr 1

end Trace

end KVAC.Schemes.MicroCMZ
