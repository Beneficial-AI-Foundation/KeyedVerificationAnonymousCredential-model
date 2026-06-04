/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Core.AlgebraicMAC.Construction
import VCVio

/-!
# UF-CMVA security predicate for an algebraic MAC (O24 Figure 5)

Game-based unforgeability under chosen-message-and-verify-attack
(UF-CMVA) for an `AlgebraicMACSyntax ProbComp`, following Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint
2024/1552, Figure 5.

The game gives the adversary `OracleComp` access to two oracles —
**Sign** (the honest MAC oracle) and **Verify** (the honest verification
oracle) — and tracks the messages signed so far in a `SignedLog`. The
adversary wins by producing a fresh message-tag pair `(m*, σ*)` such
that `m*` was never signed and `verify(sk, m*, σ*) = true`.

## Layout

- `UFQuery` — an inductive type enumerating the two oracle arms.
- `UFOracleSpec` — the `OracleSpec` parametrised by `UFQuery`.
- `UFAdversary` — adversaries: `OracleComp`-valued programs that take
  `(crs, pp)` and return a forgery `(m*, σ*)`.
- `SignedLog` — list of message vectors signed during the game.
- `ufOracleImpl` — `QueryImpl` that honestly implements Sign and Verify
  for a fixed secret key, threading the `SignedLog` via `StateT`.
- `UF_CMVAGame` — the experiment as a `ProbComp Bool`.
- `UF_CMVAAdv` — the UF-CMVA advantage `Pr[= true | UF_CMVAGame]`.

The advantage is the object security theorems will bound. A scheme is
UF-CMVA-secure if `UF_CMVAAdv mac A secParam n` is negligible in
`secParam` for every PPT adversary `A`. Asymptotic / negligibility
statements are deferred to later tracks (Pre #2, CMZ-S #10, BBS-S #15).
-/

namespace KVAC.Core

open OracleSpec OracleComp ENNReal

variable {secParam n : Nat}

/--
The two oracle arms a UF-CMVA adversary can query against an algebraic
MAC for a fixed `crs`:

- `sign m` — request a fresh MAC tag on the attribute vector `m`.
- `verify m σ` — ask whether `σ` is a valid tag for `m`.

The inductive is indexed by `mac` and `crs` so that the message-vector
and tag types refer to the concrete CRS.
-/
inductive UFQuery (mac : AlgebraicMACSyntax ProbComp)
    (crs : mac.Crs secParam n) : Type where
  | sign : MsgVec mac crs → UFQuery mac crs
  | verify : MsgVec mac crs → mac.Tag crs → UFQuery mac crs

/--
The `OracleSpec` for UF-CMVA: each `UFQuery` arm maps to the response
type the adversary expects.

- `sign m` ↦ `mac.Tag crs`
- `verify m σ` ↦ `Bool`
-/
def UFOracleSpec (mac : AlgebraicMACSyntax ProbComp)
    (crs : mac.Crs secParam n) : OracleSpec (UFQuery mac crs)
  | .sign _ => mac.Tag crs
  | .verify _ _ => Bool

/--
A UF-CMVA adversary: a program that, given the CRS and the public
parameters, queries the Sign / Verify oracles and outputs a candidate
forgery `(m*, σ*)`.
-/
structure UFAdversary (mac : AlgebraicMACSyntax ProbComp) where
  run : {secParam n : Nat} → (crs : mac.Crs secParam n) → mac.Pp crs →
    OracleComp (UFOracleSpec mac crs) (MsgVec mac crs × mac.Tag crs)

/--
The list of message vectors the adversary has had MAC'd so far during a
UF-CMVA experiment. Threaded as `StateT` state through `ufOracleImpl`,
and consulted at the end of the game to decide whether the adversary's
forgery is fresh.
-/
abbrev SignedLog (mac : AlgebraicMACSyntax ProbComp)
    (crs : mac.Crs secParam n) : Type :=
  List (MsgVec mac crs)

/--
Honest implementation of the UF-CMVA oracles for a fixed secret key
`sk`. The Sign branch runs `mac.MAC` and prepends the queried message
vector to the log; the Verify branch runs `mac.verify` and leaves the
log unchanged.
-/
def ufOracleImpl (mac : AlgebraicMACSyntax ProbComp)
    (crs : mac.Crs secParam n) (sk : mac.Sk crs) :
    QueryImpl (UFOracleSpec mac crs) (StateT (SignedLog mac crs) ProbComp)
  | .sign m => StateT.mk fun signed =>
      mac.MAC crs sk m >>= fun sig => pure (sig, m :: signed)
  | .verify m sig => StateT.mk fun signed =>
      pure (mac.verify crs sk m sig, signed)

/--
The UF-CMVA experiment (O24 Figure 5) as a `ProbComp Bool`. Runs the
adversary with oracle access via `ufOracleImpl`, recovers the forgery
`(m*, σ*)` and the resulting `SignedLog`, and returns `true` iff `m*`
is fresh and `verify(sk, m*, σ*) = true`.
-/
def UF_CMVAGame (mac : AlgebraicMACSyntax ProbComp) (A : UFAdversary mac)
    (secParam n : Nat) : ProbComp Bool := do
  let crs ← mac.setup secParam n
  let (sk, pp) ← mac.keygen crs
  let ((mStar, sigStar), signed) ←
    ((simulateQ (ufOracleImpl mac crs sk) (A.run crs pp)).run [])
  let fresh := decide (mStar ∉ signed)
  pure (fresh && mac.verify crs sk mStar sigStar)

/--
The UF-CMVA advantage of an adversary `A` against `mac` at parameters
`secParam` and `n`: the probability that `UF_CMVAGame` returns `true`.

A scheme is UF-CMVA-secure if this advantage is negligible in `secParam`
for every PPT adversary; the asymptotic / negligibility statement lives
in later tracks.
-/
noncomputable abbrev UF_CMVAAdv (mac : AlgebraicMACSyntax ProbComp)
    (A : UFAdversary mac) (secParam n : Nat) : ℝ≥0∞ :=
  Pr[= true | UF_CMVAGame mac A secParam n]

end KVAC.Core
