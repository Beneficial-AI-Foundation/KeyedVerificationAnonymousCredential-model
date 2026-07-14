/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

/-!
# μCMZ AGM unforgeability — the `n = 1` reduction (O24 §5.3, Lemma 5.4)

The reduction layer that connects the game (`KVAC.Schemes.MicroCMZ.AlgebraicMAC`)
to the polynomial backbone (`KVAC.Schemes.MicroCMZ.AGMPolynomial`). Its `Core`
part (the only part on this branch) provides:

- `AGMRepr.toReprCoeffs` / `gamePoint` — the game ↔ polynomial dictionary;
- `agmRepr_eval_eq_eval_toPoly` — the **eval bridge**: a representation's group
  evaluation equals its `ReprCoeffs.toPoly` evaluated at the transcript's
  discrete-log point, scaled onto `gen`;
- `agm_n1_identity_Ustar_eq_zero` — the **identity branch**: a fresh forgery whose
  verification polynomial vanishes identically forces `U* = 0`, which
  `microCMZVerify` rejects (`U* ≠ 0`);
- `recoverDlog` / `recoverDlog_eq` — the reduction's **discrete-log extraction**:
  among `ψ`'s `≤ 3` roots, the unique one hitting the challenge `X` is `log_gen X`
  (honest — never uses `glog`);
- `recoverDlog_verifPoly_eq` — the **win-implies-extract** step: when the
  verification equation holds at the embedded point and `ψ ≠ 0`, the reduction
  outputs the challenge exponent `x`;
- `reductionOracleImpl` / `microCMZ3DLReduction` — the reduction adversary and its
  simulated oracle: runs `A` with no `sk`, then extracts the challenge exponent
  from `ψ`'s roots.

The non-identity probability bound (3-DL + Schwartz–Zippel) and the security
theorems (O24 Lemma 5.4 / Theorem 5.1) are assembled by the forthcoming parts of
the stack (not this branch).

This is a separate module from `AlgebraicMAC` on purpose: it imports
`AGMPolynomial`, whose `MvPolynomial`/`Polynomial` order instances would derail
the `Module F`-instance search behind the `gen`-bijectivity `Fact` (`· • gen`).
Keeping that in `AlgebraicMAC` — which does *not* import `AGMPolynomial` — lets it
elaborate cleanly; here we only *use* the resulting `glog`, so nothing re-triggers
that search.

The reduction states its bad-event bound as `deg ψ / p = 3/p` (Schwartz–Zippel on
the degree-≤3 masked univariate `ψ`), not the `1/p` O24 prints; the full argument
accompanies the bound where it is proven downstream.
-/

/-!
This file is an aggregator: the μCMZ AGM reduction lives in the `AGMReduction/`
subdirectory (Core, Coupling, DeterministicCore, Assembly, Shear, ShearShift,
Security), split so each unit is reviewable. Importing this file brings the whole
reduction into scope, exactly as the former single module did.
-/
