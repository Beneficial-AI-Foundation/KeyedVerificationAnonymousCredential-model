/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

/-!
# μCMZ AGM unforgeability — the `n = 1` reduction (Lemma 5.4, O24 §5.3)

Connects the game (`AlgebraicMAC`) to the polynomial backbone (`AGMPolynomial`).
The `Core` part here provides:

- `AGMRepr.toReprCoeffs` / `gamePoint` — the game ↔ polynomial dictionary;
- `agmRepr_eval_eq_eval_toPoly` — the eval bridge: a representation's group
  evaluation equals `ReprCoeffs.toPoly` at the transcript's discrete-log point;
- `agm_n1_identity_Ustar_eq_zero` — the identity branch: a fresh forgery with an
  identically-vanishing verification polynomial forces `U* = 0`, which
  `MicroCMZ.verify` rejects;
- `recoverDlog` / `recoverDlog_eq` — discrete-log extraction: the unique root of
  `ψ` hitting the challenge `X` is `log_gen X` (never uses `glog`);
- `recoverDlog_verifPoly_eq` — win implies extract: when the verification equation
  holds at the embedded point and `ψ ≠ 0`, the reduction outputs `x`;
- `reductionOracleImpl` / `microCMZ3DLReduction` — the reduction adversary and its
  simulated oracle: runs `A` with no `sk`, then extracts `x` from `ψ`'s roots.

This file is the aggregator: the reduction lives in the `AGMReduction/`
subdirectory, and `Core` is its only part so far. The probability bound (3-DL +
Schwartz–Zippel) and the security theorems land in later parts, so Lemma 5.4 is
untagged here until that bound arrives.

The module is separate from `AlgebraicMAC` because importing `AGMPolynomial` arms
the order-instance hazard (see the `glog` note in `AlgebraicMAC.lean`); here we
only *use* the sealed `glog`.

**Two departures from O24's printed bound.** Lemma 5.4 states
`Adv^{3-dl} + Adv^{dl} + 1/p` (p. 36), and the bound assembled here is
3-DL + `3/p`.

- The bad-event bound is `deg ψ / p = 3/p` (Schwartz–Zippel on the degree-≤3
  `ψ`), not the `1/p` O24 prints (`docs/DESIGN_ALTERNATIVES.md`).
- The `Adv^dl` summand is dropped: Lemma 5.4's proof (pp. 36–38) builds only the
  3-DL reduction and no DL reduction, so the summand is left unjustified — in
  O24 it survives only as nonnegative slack. Lemma 5.5's gap-DL term is *not*
  this term: it is a separate `n = poly` argument (its case (i) collision branch,
  via Thm 5.6), and there is no collision branch at `n = 1`. See
  `docs/presentations/rolf-status/errata.md` §6.
-/
