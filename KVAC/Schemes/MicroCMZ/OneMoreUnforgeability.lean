/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Polynomial
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
- `Statements` — the Theorem 5.11 target statements, `sorry`d: the named bounds
  `omufBoundN1` and `omufBound`, the named reduction stubs, `agm_omuf_le_n1` at
  `n = 1` (Equation 23) and `agm_omuf_le` for every `n`.

The game transcript the polynomials are read off and the Claims 5.12 to 5.14
follow as further parts. The plain Figure 6 game of
`KVAC.Preliminaries.AnonymousTokens.Security` is reached from the AGM game by a
deferred bridge (Phase B of the plan).
-/
