/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Preliminaries.Assumptions
import KVAC.Schemes.MicroCMZ.Construction
import Mathlib.Tactic.Module
import VCVio

/-!
# μCMZ as an algebraic MAC — AGM game and sign-oracle scaffolding (O24 §5.3)

This file sets up the **algebraic group model** (AGM) UF-CMVA game for the μCMZ
base MAC (`KVAC.Schemes.MicroCMZ.μCMZBaseMAC`), following Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552, §5.3. It is the
`AGMPolynomial`-free foundation layer: it provides the definitions and the
distribution lemmas that the reduction consumes, but *not* the reduction itself.

## What is in this file

- **Discrete-log machinery** over the generator `gen` — `glog` and its inverse
  laws (`glog_smul`, `glog_smul_self`), used to write uniform transcript
  elements as scalar multiples of `gen`.
- **The AGM representation** — `AGMRepr` (coefficients over the transcript basis)
  and its evaluator `AGMRepr.eval`.
- **The instrumented game** — `AGMOracleSpec`, `agmOracleImpl`, `AGMUFAdversary`,
  `AGM_UF_CMVAGame`, and the advantage `AGM_UF_CMVAAdv`. The honest `sign` /
  `verify` arms delegate to `(μCMZBaseMACSyntax F gen).MAC` / `.verify` (the
  scheme adapter from `Construction.lean`); `help` uses the μCMZ `sk` directly.

The sign-arm distribution lemmas that the reduction consumes (showing its `sign`
oracle samples `Uⱼ` uniformly over `G^×`, matching the real oracle exactly) live
in the sibling module `KVAC.Schemes.MicroCMZ.SignMask`, not here — they share
this file's `AGMPolynomial`-free instance context but were split out to keep this
file focused on the game definitions.

## The AGM, mechanized scheme-specifically

We follow the standard mechanization of the AGM: it is a restriction on the
adversary *class*, encoded as an instrumented game. Every group element the
adversary submits (in `Verify` / `Help` queries and in the final forgery) must
be accompanied by an **algebraic representation**: coefficients over the
transcript basis of elements received so far —

  `G₀` (generator), `H` (crs), `X₀, Xᵣ, X⃗` (pp), and `(Uⱼ, Vⱼ)` per Sign query.

The instrumented oracles check the representation against the current
transcript and answer honestly iff it is consistent (otherwise `false`); the
win condition likewise requires the forgery representations to be consistent.
This is exactly the interface the Lemma 5.4 reduction needs: it answers
`Verify`/`Help` by evaluating the represented polynomial (degree ≤ 3) at the
embedded 3-DL instance.

Representations are *lists* of tag coefficients (one `(αᵤ, αᵥ)` pair per Sign
query made so far, `zipWith`-evaluated against the issued tags), avoiding
dependently-typed oracle queries; coefficients beyond the issued tags are
ignored by evaluation.

## Stronger game: the `Help` oracle

Per O24 §5.2/§5.3, unforgeability is proved for the *stronger* game where the
adversary additionally gets `Help(A₀, A⃗, Z)`, answering whether
`Z = (x₀ + xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ`. This strengthening does not change the bound
and is consumed by the credential-level extractability proof (O24 Thm 5.11 /
Thm 5.2).

## Bound fidelity (context for the deferred bound)

When the reduction states the bound (in `AGMReduction`), note that O24 prints
Lemma 5.5 / Theorem 5.1 as `Adv ≤ Adv^{3-dl} + Adv^{dl} + 3/p`, but its own
accounting (Claims 5.6, 5.7 + Lemma 5.4) produces an additional `Adv^{gap-dl}`
term that the printed bound elides. The Lean statement carries the gap-DL term
explicit (sound either way); tightening is deferred to the proof track.

## Downstream work (not this file)

- Claims 5.6 / 5.7 as standalone sub-lemmas (they bound the two forgery cases
  `Σᵢm*ᵢXᵢ = ΣᵢmⱼᵢXᵢ` / `≠`).
- Bridging lemma: an algebraic adversary that never submits an inconsistent
  representation and ignores `Help` wins the plain `UF_CMVAGame` of
  `KVAC.Core` exactly as often as this instrumented game.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-! ## Discrete logarithm over the generator `gen`

The scalar-multiplication map `(· • gen) : F → G` is taken to be a bijection via
`hgen : Fact (Function.Bijective (· • gen))`. In a prime-order group this holds
for any nonzero `gen`; we carry it as a hypothesis rather than re-derive
surjectivity, whose `IsSimpleAddGroup` / `LinearMap.range` instance search does
*not* terminate in this module's import context. The downstream reduction
discharges `hgen` at a concrete `gen` (a DL / 3-DL challenge base); `gen ≠ 0`
follows (`gen_ne_zero`).

Bijectivity yields the discrete-log function `glog : G → F` (the paper's `logG`),
used by the AGM reduction to write uniformly-sampled transcript elements (`H`, the
tags `Uⱼ`) as scalar multiples of `gen`. -/

variable (gen : G)

/-- Scalar multiplication by a nonzero group element is injective over a field. -/
theorem smul_left_injective_of_ne_zero {g : G} (hg : g ≠ 0) :
    Function.Injective (fun x : F => x • g) := by
  intro a b hab
  simp only at hab
  have : (a - b) • g = 0 := by rw [sub_smul, hab, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg

/- Carried as a `Fact` *instance* so it threads through the file's definitions
and instances via typeclass resolution — an explicit hypothesis would need
passing at every call site and would make the nonvanishing-mask `SampleableType`
instance below unresolvable. The downstream reduction discharges it for its
concrete generator. -/
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]

/-- The generator `gen` is nonzero: if `gen = 0` the map `(· • gen)` is constant,
contradicting the injectivity half of `hgen` over the nontrivial field `F`. -/
theorem gen_ne_zero : gen ≠ 0 := by
  intro hz
  have h : (fun x : F => x • gen) 0 = (fun x : F => x • gen) 1 := by simp [hz]
  exact zero_ne_one (hgen.out.injective h)

/-- The discrete logarithm of `y` to base `gen`: the unique scalar `x` with
`x • gen = y`. Defined via `Function.invFun` so it depends only on `gen` (not on
the bijectivity proof); the inverse laws below consume `hgen`. -/
noncomputable def glog (y : G) : F :=
  Function.invFun (fun x : F => x • gen) y

theorem glog_smul (y : G) : (glog gen y : F) • gen = y :=
  Function.invFun_eq (hgen.out.surjective y)

theorem glog_smul_self (x : F) : glog gen (x • gen) = x :=
  Function.leftInverse_invFun hgen.out.injective x

/-! ## Algebraic representations -/

/--
An algebraic representation of a group element (O24 §5.3, the adversary's `~`
coefficients) over the μCMZ transcript basis: coefficients for `G₀` (generator),
`H` (crs), `X₀`, `Xᵣ`, `X⃗` (pp), and one `(αᵤ, αᵥ)` pair per issued tag
`(Uⱼ, Vⱼ)`. The tag coefficients are a list, so the type is independent of the
(dynamic) number of Sign queries; evaluation `zipWith`s them against the issued
tags, ignoring any excess.
-/
structure AGMRepr (F : Type) (n : ℕ) where
  /-- Coefficient of the generator `G₀`. -/
  g : F
  /-- Coefficient of the crs element `H`. -/
  h : F
  /-- Coefficient of `X₀ = x₀·H`. -/
  x0 : F
  /-- Coefficient of `Xᵣ = xᵣ·G₀`. -/
  xr : F
  /-- Coefficients of `Xᵢ = xᵢ·G₀`, `i ∈ [n]`. -/
  x : Fin n → F
  /-- Coefficients `(αᵤⱼ, αᵥⱼ)` of the issued tags `(Uⱼ, Vⱼ)`, in issuance
  order. -/
  uv : List (F × F)

/--
Evaluate a representation against a concrete transcript: the fixed basis
`(g₀, H, X₀, Xᵣ, X⃗)` plus the tags issued so far.
-/
def AGMRepr.eval (ρ : AGMRepr F n) (g₀ H X₀ Xᵣ : G) (X : Fin n → G)
    (tags : List (G × G)) : G :=
  ρ.g • g₀ + ρ.h • H + ρ.x0 • X₀ + ρ.xr • Xᵣ + (∑ i, ρ.x i • X i) +
    (List.zipWith (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2)
      ρ.uv tags).sum

/-! ## The instrumented oracles -/

/--
The three oracle arms of the AGM UF-CMVA(+Help) game for μCMZ (`sign`/`verify`
from O24 Figure 5, `help` added in §5.3):

- `sign m⃗` — request a tag on `m⃗` (no representation: the adversary *receives*
  elements here).
- `verify m⃗ (U,V) ρ_U ρ_V` — verification query; the submitted tag carries
  representations.
- `help A₀ A⃗ Z ρ₀ ρ⃗ ρ_Z` — the §5.3 helper oracle, answering whether
  `Z = (x₀+xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ`; all three submitted elements carry
  representations.
-/
inductive AGMQuery (F G : Type) (n : ℕ) : Type where
  | sign : (Fin n → F) → AGMQuery F G n
  | verify : (Fin n → F) → G × G → AGMRepr F n → AGMRepr F n → AGMQuery F G n
  | help : G → (Fin n → G) → G → AGMRepr F n → (Fin n → AGMRepr F n) →
      AGMRepr F n → AGMQuery F G n

/-- Response types for `AGMQuery`: a tag for `sign`, a Boolean for `verify`
and `help`. -/
def AGMOracleSpec (F G : Type) (n : ℕ) : OracleSpec (AGMQuery F G n)
  | .sign _ => G × G
  | .verify _ _ _ _ => Bool
  | .help _ _ _ _ _ _ => Bool

/--
The transcript log threaded through the game: the messages signed so far,
each with the tag issued for it, in issuance order (`sign` appends). The
message components decide forgery freshness; the tag components extend the
representation basis.
-/
abbrev AGMLog (F G : Type) (n : ℕ) := List ((Fin n → F) × (G × G))

/--
Honest instrumented implementation of the AGM oracles for secret key `sk`,
crs `H`, and public parameters `pp = (X₀, Xᵣ, X⃗)`. The `sign` / `verify` arms
delegate to the `AlgebraicMACSyntax` interface value `μCMZBaseMACSyntax F gen`
(the seam this game crosses); `help` (O24 §5.3, scheme-specific depth) does not use
the interface — it destructures the concrete μCMZ `sk` directly for the equation
`Z = (x₀+xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ`, which is the visible signal of the scheme-specific
depth behind the seam.

- `sign` runs `(μCMZBaseMACSyntax F gen).MAC` and appends `(m⃗, σ)` to the log;
- `verify` checks the representations against the current transcript and returns
  `(μCMZBaseMACSyntax F gen).verify` iff they are consistent (else `false`);
- `help` answers the linear-form query, using `sk` directly.
-/
noncomputable def agmOracleImpl (secParam : ℕ) (sk : F × F × (Fin n → F)) (H : G)
    (pp : G × G × (Fin n → G)) :
    QueryImpl (AGMOracleSpec F G n) (StateT (AGMLog F G n) ProbComp)
  | .sign m => StateT.mk fun log => do
      let σ : G × G ← (μCMZBaseMACSyntax F gen).MAC (secParam := secParam) H sk m
      pure (σ, log ++ [(m, σ)])
  | .verify m σ ρU ρV => StateT.mk fun log =>
      let tags := log.map Prod.snd
      let consistent :=
        ρU.eval (gen) H pp.1 pp.2.1 pp.2.2 tags = σ.1 ∧
        ρV.eval (gen) H pp.1 pp.2.1 pp.2.2 tags = σ.2
      pure (decide consistent &&
        (μCMZBaseMACSyntax F gen).verify (secParam := secParam) H sk m σ, log)
  | .help A₀ A Z ρ₀ ρA ρZ => StateT.mk fun log =>
      let tags := log.map Prod.snd
      let consistent :=
        ρ₀.eval (gen) H pp.1 pp.2.1 pp.2.2 tags = A₀ ∧
        (∀ i, (ρA i).eval (gen) H pp.1 pp.2.1 pp.2.2 tags = A i) ∧
        ρZ.eval (gen) H pp.1 pp.2.1 pp.2.2 tags = Z
      pure (decide consistent &&
        decide (Z = (sk.1 + sk.2.1) • A₀ + ∑ i, sk.2.2 i • A i), log)

/-! ## The game -/

/--
An algebraic UF-CMVA adversary against μCMZ for `n` attributes (O24 §5.3): given
the crs `H` and public parameters `(X₀, Xᵣ, X⃗)`, it queries the instrumented
oracles and outputs a forgery `(m⃗*, (U*, V*))` together with representations of
`U*` and `V*` over the final transcript.
-/
structure AGMUFAdversary (F G : Type) (n : ℕ) where
  run : G → G × G × (Fin n → G) →
    OracleComp (AGMOracleSpec F G n)
      ((Fin n → F) × (G × G) × AGMRepr F n × AGMRepr F n)

/--
The AGM UF-CMVA(+Help) experiment for μCMZ (O24 Figure 5, instrumented per
§5.3). Setup and keygen are delegated to the `AlgebraicMACSyntax` interface
value `μCMZBaseMACSyntax F gen` (the seam this game crosses); the adversary runs
against `agmOracleImpl`; the experiment returns `true` iff the forgery
representations are consistent with the final transcript, the forged message is
fresh, and the forgery verifies (via the interface's `verify`).
-/
noncomputable def AGM_UF_CMVAGame (secParam : ℕ) (A : AGMUFAdversary F G n) :
    ProbComp Bool := do
  let mac := μCMZBaseMACSyntax F gen
  let H : G ← mac.setup secParam n
  let (sk, pp) ← (mac.keygen (secParam := secParam) (n := n) H :
      ProbComp (Key F n × Params G n))
  let ((mStar, σStar, ρU, ρV), log) ←
    (simulateQ (agmOracleImpl (gen := gen) secParam sk H pp) (A.run H pp)).run []
  let tags := log.map Prod.snd
  let consistent :=
    ρU.eval (gen) H pp.1 pp.2.1 pp.2.2 tags = σStar.1 ∧
    ρV.eval (gen) H pp.1 pp.2.1 pp.2.2 tags = σStar.2
  let fresh := mStar ∉ log.map Prod.fst
  pure (decide consistent && decide fresh &&
    mac.verify (secParam := secParam) H sk mStar σStar)

/-- The AGM UF-CMVA(+Help) advantage: `Pr[= true | AGM_UF_CMVAGame …]`, a function
of `secParam` (kept as a function of `secParam` so the negligibility statement,
deferred to the proof track, can quantify over it). -/
noncomputable abbrev AGM_UF_CMVAAdv (A : AGMUFAdversary F G n) (secParam : ℕ) : ℝ≥0∞ :=
  Pr[= true | AGM_UF_CMVAGame (gen := gen) secParam A]

/-! ## Security statements (O24 §5.3)

The `n = 1` reduction scaffold (the `AGMRepr ↔ ReprCoeffs` eval bridge, the
mechanized identity-branch contradiction, and the restructured security
theorems `agm_ufcmva_le_n1` / `agm_ufcmva_le`) is delivered in a separate,
forthcoming module `KVAC.Schemes.MicroCMZ.AGMReduction` (not part of this
branch). It is split into its own file because it
imports `AGMPolynomial`, whose polynomial-order instances would otherwise derail
the `Module F`-instance search behind `glog`'s inverse laws (`glog_smul`) above
(the bridge needs `glog`, but `glog`'s *proof* must elaborate without those
instances in scope).

**Bridging lemma (deferred to the proof track).** The theorem relating this
instrumented game to the plain `UF_CMVAGame` of `KVAC.Core.AlgebraicMAC.Security`
— an algebraic adversary that never submits an inconsistent representation and
ignores `Help` wins the plain game exactly as often as this instrumented game —
is *not* stated on this branch. Its statement needs a runtime `WellBehaved`
predicate (representations consistent across the live transcript) and a
`project : AGMUFAdversary → UFAdversary` oracle-program translation, both coupled
to the reduction's formalization; stubs plus `sorry` would validate nothing. The
prerequisite the bridge depends on — both `UF_CMVAGame` and `AGM_UF_CMVAGame`
crossing the `AlgebraicMACSyntax` seam at the adapter `μCMZBaseMACSyntax F gen` —
is delivered by this branch (the game delegates setup/keygen/MAC/verify to the
interface value, no longer inlining them behind `rfl`-aliases). -/

end KVAC.Schemes.MicroCMZ
