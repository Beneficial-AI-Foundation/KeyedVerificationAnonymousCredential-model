/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

/-!
# μCMZ AGM unforgeability — the `n = 1` reduction (O24 §5.3, Lemma 5.4)

Connects the game (`AlgebraicMAC`) to the polynomial backbone (`AGMPolynomial`).
The `Core` part here provides:

- `AGMRepr.toReprCoeffs` / `gamePoint` — the game ↔ polynomial dictionary;
- `agmRepr_eval_eq_eval_toPoly` — the eval bridge: a representation's group
  evaluation equals `ReprCoeffs.toPoly` at the transcript's discrete-log point;
- `agm_n1_identity_Ustar_eq_zero` — the identity branch: a fresh forgery with an
  identically-vanishing verification polynomial forces `U* = 0`, which
  `microCMZVerify` rejects;
- `recoverDlog` / `recoverDlog_eq` — discrete-log extraction: the unique root of
  `ψ` hitting the challenge `X` is `log_gen X` (never uses `glog`);
- `recoverDlog_verifPoly_eq` — win implies extract: when the verification equation
  holds at the embedded point and `ψ ≠ 0`, the reduction outputs `x`;
- `reductionOracleImpl` / `microCMZ3DLReduction` — the reduction adversary and its
  simulated oracle: runs `A` with no `sk`, then extracts `x` from `ψ`'s roots.

The probability bound (3-DL + Schwartz–Zippel) and the security theorems are
assembled downstream.

The module is separate from `AlgebraicMAC` because importing `AGMPolynomial` arms
the order-instance hazard (see the `glog` note in `AlgebraicMAC.lean`); here we
only *use* the sealed `glog`. The bad-event bound is `deg ψ / p = 3/p`
(Schwartz–Zippel on the degree-≤3 `ψ`), not the `1/p` O24 prints.
-/

/-!
Aggregator: the reduction lives in the `AGMReduction/` subdirectory (Core,
Coupling, DeterministicCore, Assembly, Shear, ShearShift, Security). Importing
this file brings the whole reduction into scope.
-/
