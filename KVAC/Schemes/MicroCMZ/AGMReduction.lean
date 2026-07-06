/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Core

/-!
# μCMZ AGM unforgeability — the `n = 1` reduction (O24 §5.3, Lemma 5.4)

The reduction layer that connects the game (`KVAC.Schemes.MicroCMZ.AlgebraicMAC`)
to the proven polynomial backbone (`KVAC.Schemes.MicroCMZ.AGMPolynomial`):

- `AGMRepr.toReprCoeffs` / `gamePoint` — the game ↔ polynomial dictionary;
- `agmRepr_eval_eq_eval_toPoly` — the **eval bridge** (keystone, *proven*): a
  representation's group evaluation equals its `ReprCoeffs.toPoly` evaluated at
  the transcript's discrete-log point, scaled onto `generator G`;
- `agm_n1_identity_Ustar_eq_zero` — the **identity branch**, *proven*: a fresh
  forgery whose verification polynomial vanishes identically forces `U* = 0`,
  which `microCMZVerify` rejects (`U* ≠ 0`);
- `recoverDlog` / `recoverDlog_eq` — the reduction's **discrete-log extraction**,
  *proven*: among `ψ`'s `≤ 3` roots, the unique one hitting the challenge `X` is
  `log_G X` (honest — never uses `glog`);
- `recoverDlog_verifPoly_eq` — the **win-implies-extract** core, *proven*: when
  the verification equation holds at the embedded point and `ψ ≠ 0`, the
  reduction outputs the challenge exponent `x`;
- `reductionOracleImpl` / `microCMZ3DLReduction` — the **reduction adversary
  `B₃`** and its simulated oracle, *defined* (and supplied as the witness in
  `agm_ufcmva_le_n1_nonIdentityBound`): runs `A` with no `sk`, then extracts the
  challenge exponent from `ψ`'s roots;
- `agm_ufcmva_le_n1_nonIdentityBound` — the **non-identity branch** (3-DL +
  Schwartz–Zippel), now **fully proven** (kernel-verified sorry-free; axioms
  `propext`/`Classical.choice`/`Quot.sound` only): the reduction `B₃` is defined and the
  *probability inequality* is discharged — distribution-equivalence of the simulated game
  with `AGM_UF_CMVAGame` via the shear reparametrization, plus the `3/p` bad-event bound (see
  its docstring; this is `deg ψ / p`, *not* the `1/p` O24 prints — see the bound-fidelity
  note below);
- `agm_ufcmva_le_n1` / `agm_ufcmva_le` — the security theorems (O24 Lemma 5.4 /
  Theorem 5.1), restructured to compose the above.

This is a separate module from `AlgebraicMAC` on purpose: it imports
`AGMPolynomial`, whose `MvPolynomial`/`Polynomial` order instances derail the
`Module F`-instance search inside `smul_generator_bijective` (the bijectivity of
`· • generator G`). Keeping that proof in `AlgebraicMAC` — which does *not*
import `AGMPolynomial` — lets it elaborate cleanly; here we only *use* the
resulting `glog`, so nothing re-triggers that search.

## Bound fidelity (O24's `1/p` vs the `3/p` here)

O24 Lemma 5.4 prints `Adv = Adv^{3-dl} + Adv^{dl} + 1/p`, and Theorem 5.1
`… + 3/p`. The `1/p` is the bad event "`ψ ≢ 0` except w.p. `1/p`" (O24 p. 38). But
`ψ = affineSubst a b (verifPoly)` is a univariate restriction of a *degree-≤3*
polynomial to the random line `v ↦ aᵥ + χ·bᵥ`; Schwartz–Zippel bounds
`Pr[ψ ≡ 0 | verifPoly ≠ 0] ≤ deg ψ / p = 3/p` (the `χ³`-coefficient is a nonzero
degree-3 polynomial in the masks — `natDegree_affineSubst_verifPoly_le` and
`card_roots_affineSubst_verifPoly_le` both witness `deg = 3`). We therefore state
`3/p` (Lemma 5.4) and, composing Claims 5.6/5.7 (`1/p` each), `5/p` (Theorem 5.1)
— sound, and what the formal SZ argument will actually yield. O24's printed
`1/p` / `3/p` appear to undercount the SZ degree.

## TODO(CMZ-M)
- `agm_ufcmva_le_n1_nonIdentityBound`: **DONE** — kernel-verified sorry-free. The algebraic
  backbone, the reduction adversary `B₃` (`microCMZ3DLReduction`, with `reductionOracleImpl`),
  the distribution-equivalence (shear reparametrization: `redFullExtSZ_szBit_eq_shift` and the
  chain feeding it), and the `3/p` Schwartz–Zippel bad-event bound (`redFullExtSZ_szBit_le`)
  are all in place.
- `agm_ufcmva_le`: the general-`n` case (reduces to `n = 1` + gap-DL) — the sole remaining
  `sorry` in this module.
-/

/-!
This file is an aggregator: the μCMZ AGM reduction lives in the `AGMReduction/`
subdirectory (Core, Coupling, DeterministicCore, Assembly, Shear, ShearShift,
Security), split so each unit is reviewable. Importing this file brings the whole
reduction into scope, exactly as the former single module did.
-/
