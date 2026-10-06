/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Polynomial
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Transcript
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.CaseEvents
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Statements

/-!
# μCMZ_AT one-more unforgeability (O24 §5.6, Theorem 5.11)

Aggregator for the one-more unforgeability analysis of the μCMZ_AT core scheme
(`ATVariant.lean`), which lives in the `OneMoreUnforgeability/` subdirectory on
the pattern of `AGMReduction/`. Track CMZ-OMUF of the Theorem 5.3 plan. Each part
documents its own contents in its module docstring:

- `Game` — the AGM-instrumented one-more unforgeability game: the representation
  gate, the query type and log, the gated Sign and Verify oracles, the algebraic
  adversary and its forgeries, the winning condition, the experiment
  `AGM_OMUFGame` and its advantage;
- `Polynomial` — the pure-algebra layer of Equations 17 to 22 over the ring of
  `AGMPolynomial.lean`: the exponent of a representation given the commitment
  polynomials, the commitment polynomials `c_1, …, c_r` (Equations 17 and 18),
  the forgery polynomial `φ` (Equation 22), and the three variable groups of
  the proof's case split;
- `Transcript` — the trace of a run of the game with the decision left out,
  and the game as trace plus decision;
- `CaseEvents` — the polynomials of Equations 18 and 22 read off a trace, and
  the win and the three case events of the proof's case split, items (i) to
  (iii), that Claims 5.12 to 5.14 bound;
- `Statements` — the Theorem 5.11 target statements, `sorry`d: the named bounds
  `omufBoundN1` and `omufBound`, the named reduction stubs (the theorem's, and
  one each for Claims 5.12 and 5.13), `agm_omuf_le_n1` at `n = 1` (Equation
  23), `agm_omuf_le` for every `n`, and the Claims 5.12 to 5.14 over the case
  events of `CaseEvents`.

The plain Figure 6 game of `KVAC.Preliminaries.AnonymousTokens.Security` is
reached from the AGM game by a deferred bridge (Phase B of the plan).
-/
