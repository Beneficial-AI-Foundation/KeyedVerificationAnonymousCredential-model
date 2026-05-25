/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import VCVio.OracleComp.ProbComp

/-!
# Algebraic message authentication codes (O24 §3.2)

Abstract syntax for an algebraic message authentication code per Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
Definition 3.1.

An `AlgebraicMAC` value bundles the four algorithms of a MAC scheme — Setup,
KeyGen, MAC, Verify — into a single structure. Concrete schemes (μCMZ in §5,
μBBS in §6) are *values* of this structure rather than canonical typeclass
instances on a type, since a user can have several distinct algebraic-MAC
schemes in scope simultaneously.

## Design notes

- **Monad-polymorphic randomness.** The `setup`, `keygen`, and `MAC`
  algorithms — which the paper writes with `←$` to indicate sampling of
  random coins — return values in an abstract monad `M`. The deterministic
  `verify` algorithm returns `Bool` directly. Concrete interpretations of
  the scheme arise by instantiating `M`:
    - `M := Id` gives a fully deterministic interpretation (useful for
      tests, toy schemes, and schemes that don't model randomness).
    - `M := ProbComp` gives the probabilistic interpretation used by
      VCV-io game-based reductions in security tracks.
    - Future symbolic interpretations would plug in a different `M`
      (e.g. a Dolev-Yao term-algebra monad).
  A single scheme value supports all these interpretations by choice of `M`.
- **`n` (attribute count) is a method argument**, not a structure parameter.
  A single `AlgebraicMAC` value handles all `n`, matching the paper's setup
  signature `MAC.S(1^λ, n)`.
- **Correctness and UF-CMVA are separate obligations**, not structure
  fields. Both are proved per scheme as standalone theorems. This trades
  the by-construction correctness guarantee of bundled correctness (cf.
  PQXDH's `KEM`) for two benefits: (a) the structure stays monad-
  polymorphic, since correctness statements differ in shape between `Id`
  (Bool equation) and `ProbComp` (`evalDist`-based); (b) different
  correctness *variants* (functional correctness, robustness, …) can be
  proved without bloating the structure.

## Out of scope here

- **Correctness theorems** (O24 §3.2). Stated per scheme alongside the
  scheme's definition, in the appropriate form for the chosen monad `M`.
- **UF-CMVA security predicate** (O24 Figure 5). Deferred to Track Pre (#2)
  alongside the other hardness assumptions (DL, DDH, q-DL, q-DDHI, gap-DL),
  where it will be bound to VCV-io's `CryptoFoundations/HardnessAssumptions/`
  library.
- **Concrete schemes** (μCMZ §5, μBBS §6). Delivered by Track CMZ-M (#8) and
  Track BBS-M (#13) respectively.
-/

namespace KVAC.Core

/--
An algebraic message authentication code (MAC) following O24 Definition 3.1.

A value `mac : AlgebraicMAC M Crs Pp Sk 𝕄 Tag` packages the four MAC
algorithms with randomness internalised by the monad `M`. Type parameters:

- `M`   — monad encoding the randomness model (`Id` for deterministic,
          `ProbComp` for VCV-io probabilistic semantics, future symbolic
          monads for Dolev-Yao-style reasoning).
- `Crs` — common reference string type (output of `setup`).
- `Pp`  — public parameters type (output of `keygen`, alongside `Sk`).
- `Sk`  — secret key type.
- `𝕄`   — attribute (message) type. The MAC operates on `Fin n → 𝕄`
          (equivalent to `𝕄^n`, the paper's `m⃗ ∈ 𝕄^n`) for variable
          `n : Nat`.
- `Tag` — MAC tag type.

The five carrier types are explicit parameters since concrete schemes pick
their own representations (e.g. for μCMZ, `Sk` is a vector of scalars from
the underlying group's scalar field, `Tag` is a pair of group elements, etc.).

Correctness and UF-CMVA are proved per scheme as standalone theorems —
see the *Design notes* in this file for rationale.
-/
structure AlgebraicMAC (M : Type → Type) [Monad M] (Crs Pp Sk 𝕄 Tag : Type) where
  /-- Setup algorithm. Takes a security parameter `secParam` (the Lean
  rendering of O24's `1^λ` unary input) and attribute count `n`; returns a
  common reference string in `M`. The setup implicitly defines the attribute
  family `𝕄_crs = 𝕄`. -/
  setup : (secParam : Nat) → (n : Nat) → M Crs
  /-- Key generation. Takes a CRS, returns a secret key paired with public
  parameters in `M`. -/
  keygen : (crs : Crs) → M (Sk × Pp)
  /-- MAC algorithm. Takes the secret key and an `n`-attribute vector,
  returns a tag in `M`. `n` flows in per-call so a single `AlgebraicMAC`
  value handles all attribute counts. -/
  MAC : (n : Nat) → (sk : Sk) → (m : Fin n → 𝕄) → M Tag
  /-- Verification algorithm. Takes the secret key, an `n`-attribute vector,
  and a candidate tag; returns `true` if the tag is valid, `false` otherwise.
  Deterministic per O24 §3.2 — does not enter the monad. -/
  verify : (n : Nat) → (sk : Sk) → (m : Fin n → 𝕄) → (σ : Tag) → Bool

/--
Probabilistic algebraic-MAC interpretation: an `AlgebraicMAC` whose monad
parameter is `ProbComp` (VCV-io's probabilistic-computation monad). This is
the shape security tracks (CMZ-M, CMZ-A, …) work with directly when
constructing game-based experiments.
-/
abbrev ProbAlgebraicMAC (Crs Pp Sk 𝕄 Tag : Type) : Type :=
  AlgebraicMAC ProbComp Crs Pp Sk 𝕄 Tag

end KVAC.Core
