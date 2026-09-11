/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core
import KVAC.Schemes.MicroCMZ.AGMReduction.Coupling
import KVAC.Schemes.MicroCMZ.AGMReduction.SignCoupling
import KVAC.Schemes.MicroCMZ.AGMReduction.RedFull
import KVAC.Schemes.MicroCMZ.AGMReduction.SecurityN1

/-!
# μCMZ AGM unforgeability — the `n = 1` reduction (Lemma 5.4, O24 §5.3)

Aggregator for the reduction, which lives in the `AGMReduction/` subdirectory.
It connects the game (`AlgebraicMAC`) to the polynomial backbone
(`AGMPolynomial`). Each part documents its own contents in its module docstring:

- `Core` — the game ↔ polynomial dictionary, the eval bridge, the identity
  branch, the reduction adversary with its simulated oracle and run trace, and
  root recovery;
- `Coupling` — the first probability-layer slice: the uniformity and relational
  coupling bricks, the reduction ↔ honest state invariant, and the **static**
  Schwartz–Zippel core;
- `SignCoupling` — the deterministic core of the coupling: the sign-step
  coupling triple (Eq. 14) and the transcript log invariants it establishes,
  plus the two lemmas at abstract arity derived from the embedding — the
  consistency⇒vanishing step (Eq. 12 evaluated in the relative discrete
  logarithms) and the represented-value bridge the `verify`/`help` arms
  consume;
- `RedFull` — the analysis experiment `redFull`: the reduction's run at the
  genuine challenge powers, returning the record `RedBits` (win, extraction,
  Schwartz–Zippel bad and shift bits);
- `SecurityN1` — the Lemma 5.4 target bound `agm_ufcmva_le_n1_explicit`
  (still `sorry`d) and the sub-lemmas it is assembled over.

Lemma 5.4 stays untagged here until the theorem is sorry-free.

**Why this is not in `AlgebraicMAC`.** Importing `AGMPolynomial` arms the
order-instance hazard (see the `glog` note in `AlgebraicMAC.lean`); here we
only *use* the sealed `glog`.

**Two departures from O24's printed bound.** Lemma 5.4 states
`Adv^{3-dl} + Adv^{dl} + 1/p` (p. 36), and the planned target bound is
3-DL + `3/p`.

- The bad-event bound is `3/p`, not the `1/p` O24 prints: Schwartz–Zippel is
  applied to the degree-`≤ 3` *multivariate* `verifPoly` — the `C★` shift lemma
  in `Coupling` routes around the univariate `ψ` — so the bad event costs
  `deg verifPoly / p ≤ 3/p` (`docs/DESIGN_ALTERNATIVES.md`).
- The `Adv^dl` summand is dropped: Lemma 5.4's proof (pp. 36–38) builds only the
  3-DL reduction and no DL reduction, so the summand is left unjustified — in
  O24 it survives only as nonnegative slack. Lemma 5.5's gap-DL term is *not*
  this term: it is a separate `n = poly` argument (its case (i) collision branch,
  via Claim 5.6), and there is no collision branch at `n = 1`. See
  `docs/presentations/rolf-status/errata.md` §6.
-/
