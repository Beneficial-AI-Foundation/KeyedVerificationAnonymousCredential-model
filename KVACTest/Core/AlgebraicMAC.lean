/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.AlgebraicMAC
import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests / examples for `KVAC.Core.AlgebraicMAC`

This file demonstrates the API of `AlgebraicMAC` with minimal examples.
These are **not** secure or meaningful schemes — they exist purely to
(i) verify the structure can be instantiated, (ii) serve as a worked
reference for future contributors implementing real schemes (μCMZ in
Track CMZ-C #6, μBBS in Track BBS-C #7), and (iii) catch regressions if
the API changes.

Two examples are provided, demonstrating two different monad
interpretations:

- `trivial` uses `M := Id` — fully deterministic interpretation.
  Correctness is bundled as a separate theorem proved by `rfl`.
- `linearToy` uses `M := ProbComp` — VCV-io's probabilistic-computation
  monad, with randomness sampled via `$ᵗ`. Its correctness theorem is
  stated semantically over `support`, because probabilistic correctness in
  `ProbComp` cannot be stated as the syntactic equation
  `(do {…}) = pure true` (the free-monad structure of `ProbComp` preserves
  `bind` nodes, so a syntactic equality with `pure true` does not hold).

Correctness for each example is stated as a *separate theorem* below the
scheme definition, per the design decision documented in
`KVAC/Core/AlgebraicMAC.lean`.
-/

namespace KVACTest.Core.AlgebraicMAC

open KVAC.Core

/-! ## Trivial scheme over `Unit`

The simplest possible instance: every type is `Unit`, every operation
returns `()`, and `verify` always accepts. Sanity check that the structure
compiles and can be constructed end-to-end. -/

def trivial : AlgebraicMAC Id Unit Unit Unit Unit Unit where
  setup _ _ := pure ()
  keygen _ := pure ((), ())
  MAC _ _ _ := pure ()
  verify _ _ _ _ := true

/-- Deterministic correctness for `trivial`: the do-block that sets up,
keygens, MACs, and verifies always returns `true`. -/
theorem trivial_correctness :
    ∀ (secParam n : Nat) (m : Fin n → Unit),
      (do
        let crs ← trivial.setup secParam n
        let (sk, _) ← trivial.keygen crs
        let σ ← trivial.MAC n sk m
        pure (trivial.verify n sk m σ) : Id Bool)
      = pure true := by
  intros; rfl

example : trivial.verify 3 () (fun _ => ()) () = true := rfl

example : trivial.MAC 3 () (fun _ => ()) = pure () := rfl

/-! ## A toy linear MAC over `ZMod 7`, with VCV-io probabilistic semantics

A pair-shaped tag scheme mirroring the *shape* of real algebraic MACs
(such as μCMZ's `(U, U')` tag), instantiated in `M := ProbComp` so that
randomness is genuinely sampled via VCV-io's `$ᵗ` operator.

The MAC of attribute vector `m₀, …, m_{n−1}` with sampled secret key `sk`
and sampled nonce `r` is the pair `(r, sk + (Σᵢ mᵢ) + r)`. Verification
recomputes the second component and checks equality with the recorded
value.

**Warning — not secure.** The MAC is linear in `sk`: observing two MACs on
known attribute vectors lets an attacker eliminate `sk` algebraically.
This example illustrates the API and the rough *shape* of an algebraic
MAC; real schemes like μCMZ live in a prime-order group and use scalar
multiplication precisely to avoid this attack.

**Note on correctness.** `linearToy_correctness` below uses a semantic
support statement rather than syntactic equality:

- The syntactic equation `(do {…}) = (pure true : ProbComp Bool)` is **not
  provable** — `ProbComp` is a free monad over a polynomial functor, and
  `bind ma (fun _ => pure b) ≠ pure b` as a `ProbComp` term, even though
  the two have the same distribution.
- The right statement uses `evalDist (do {…}) = evalDist (pure true)` or
  `∀ b ∈ support (do {…}), b = true`. This example proves the support
  form using VCV-io's `support` lemmas. Later security theorems,
  advantages, indistinguishability, uniformity, and exact probability
  claims should use `evalDist` or `Pr[...]` instead. -/

def linearToy : AlgebraicMAC ProbComp Unit Unit (ZMod 7) (ZMod 7) (ZMod 7 × ZMod 7) where
  setup _ _ := pure ()
  keygen _ := do
    let sk ← $ᵗ (ZMod 7)
    pure (sk, ())
  MAC _ sk m := do
    let r ← $ᵗ (ZMod 7)
    pure (r, sk + (∑ i, m i) + r)
  verify _ sk m σ := decide (σ.2 = sk + (∑ i, m i) + σ.1)

/-- Sanity check: `linearToy.verify` accepts a tag of the correct shape. -/
example (sk r : ZMod 7) (m : Fin 2 → ZMod 7) :
    linearToy.verify 2 sk m (r, sk + (∑ i, m i) + r) = true := by
  simp [linearToy]

/-- Probabilistic correctness for `linearToy`: every output in the support of
the setup/keygen/MAC/verify experiment is accepting. The stronger syntactic
equality with `pure true` is intentionally not stated for `ProbComp`. -/
theorem linearToy_correctness :
    ∀ (secParam n : Nat) (m : Fin n → ZMod 7),
      ∀ b ∈ support
        (do
          let crs ← linearToy.setup secParam n
          let (sk, _) ← linearToy.keygen crs
          let σ ← linearToy.MAC n sk m
          pure (linearToy.verify n sk m σ) : ProbComp Bool),
        b = true := by
  intro secParam n m b hb
  simpa [linearToy] using hb

end KVACTest.Core.AlgebraicMAC
