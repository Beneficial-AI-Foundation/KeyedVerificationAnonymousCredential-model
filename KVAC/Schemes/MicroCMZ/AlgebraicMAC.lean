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
# μCMZ as an algebraic MAC: AGM game scaffolding (O24 §5.3)

Instrumented scaffolding for the algebraic group model (AGM) UF-CMVA(+Help) game
of the μCMZ base MAC (`μCMZBaseMAC`), following Orrù, *Revisiting
Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552, §5.3. This is
the `AGMPolynomial`-free foundation: the game definitions the Lemma 5.4 reduction
consumes, but not the reduction itself (that lands in `AGMReduction`), and not the
sign-arm distribution lemmas (those live in the sibling module `SignMask`).

A word of caution on naming: this is scaffolding, not the honest game. The
oracles here are *gated* — they answer honestly only when the submitted
representation is consistent, and return `false` otherwise. So the game matches
the honest UF-CMVA game only for *well-behaved* adversaries, the ones that never
submit an inconsistent representation. Closing that gap is the job of the
`WellBehaved` bridging lemma; that equivalence is deferred and is not proved in
this file.

Contents: `glog` discrete-log machinery over `gen`; the algebraic representation
`AGMRepr` / `AGMRepr.eval`; and the instrumented game (`AGMOracleSpec`,
`agmOracleImpl`, `AGMUFAdversary`, `AGM_UF_CMVAGame`, `AGM_UF_CMVAAdv`).

The AGM is a restriction on the adversary class: every group element the adversary
submits (in `Verify`/`Help` queries and in the forgery) carries an *algebraic
representation*, coefficients over the transcript basis received so far
(`G₀, H, X₀, Xᵣ, X⃗`, and `(Uⱼ, Vⱼ)` per Sign query). Each oracle answers honestly
iff the representation is transcript-consistent (else `false`), as does the win
condition — this is the gate. It is exactly the interface the Lemma 5.4 reduction
wants: it answers `Verify`/`Help` by evaluating the represented degree-≤3
polynomial at the embedded 3-DL instance. Gating the *answers* like this, rather
than restricting the adversary *type*, is a deliberate choice; see
`DESIGN_ALTERNATIVES.md` for the alternative we passed over. Tag coefficients are
stored as a *list* (one `(αᵤ, αᵥ)` per Sign query, `zipWith`-evaluated against
issued tags), keeping the type independent of the dynamic query count.

The `Help(A₀, A⃗, Z)` arm (O24 §5.2/§5.3) answers whether
`Z = (x₀+xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ`, the stronger notion the credential-level
extractability proof consumes (Thm 5.11 / Thm 5.2); it does not change the bound.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable {n : ℕ}

/-! ## Discrete logarithm over the generator `gen`

`(· • gen) : F → G` is taken bijective via `hgen : Fact (Function.Bijective
(· • gen))`. In a prime-order group this holds for any nonzero `gen`; we carry it
as a hypothesis because re-deriving surjectivity sends `IsSimpleAddGroup` /
`LinearMap.range` instance search non-terminating in this import context. The
reduction discharges `hgen` at a concrete DL / 3-DL challenge base (`gen ≠ 0`
follows, `gen_ne_zero`). Bijectivity yields `glog : G → F` (the paper's `logG`). -/

variable (gen : G)

/- Carried as a `Fact` *instance* so it threads through the file's definitions via
typeclass resolution; an explicit hypothesis would make the nonvanishing-mask
`SampleableType` instance unresolvable. -/
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

/-- `glog` is additive: the discrete log of a sum is the sum of the discrete
logs. With `glog_smul_scalar`, makes `glog gen` `F`-linear — the form the
reduction uses to push `glog` through `AGMRepr.eval` sums. -/
theorem glog_add (y₁ y₂ : G) :
    (glog gen (y₁ + y₂) : F) = glog gen y₁ + glog gen y₂ :=
  hgen.out.injective (by
    show glog gen (y₁ + y₂) • gen = (glog gen y₁ + glog gen y₂) • gen
    rw [glog_smul, add_smul, glog_smul, glog_smul])

/-- `glog` is homogeneous: scaling an element multiplies its discrete log. -/
theorem glog_smul_scalar (c : F) (y : G) :
    glog gen (c • y) = c * glog gen y :=
  hgen.out.injective (by
    show glog gen (c • y) • gen = (c * glog gen y) • gen
    rw [glog_smul, mul_smul, glog_smul])

/-
**Order-instance hazard — canonical note (the sealed `glog` interface).**
Downstream modules (`SignMask`, `AGMReduction.Core`) import `AGMPolynomial`, whose
`MvPolynomial`/`Polynomial` order instances put an `F`-module `G` in scope. In that
context, forcing `glog` to unfold to `Function.invFun (· • gen)` re-triggers the
`Module F` / `hgen`-bijectivity instance search, which does not terminate. `glog`'s
definition and both laws therefore live in this `AGMPolynomial`-free layer, and
downstream code must only *use* the laws (`glog_smul` / `glog_smul_self`), never
unfold `glog`.

This is the `glog`-unfold half of the hazard. Its sibling — the `$ᵗ {subtype}`
samplers, whose `SampleableType` / `Fintype` instance search loops in the same
`MvPolynomial` context — is sealed separately by `reductionMaskSample`'s
`@[irreducible]` in `SignMask`. Both seals share this note as their reference.

The `attribute [irreducible]` below enforces the `glog` invariant rather than
leaving it to convention. Note the scope: it stops the *elaborator* from unfolding
`glog`, so the elaboration-time search cannot be re-armed accidentally. It does
*not* bind the kernel — a `glog ↑U` term inside a kernel-checked (e.g. quantified)
goal can still loop the kernel, which needs the separate generalize-`glog ↑U`-to-an-
opaque-variable fix where it bites. The laws above are proved first, while `glog` is
still reducible; sealing after them keeps the interface — the function plus its two
rewrite laws — intact. Other sites that used to re-explain this hazard point here.
-/
attribute [irreducible] glog

/-! ## Algebraic representations -/

/--
An algebraic representation (O24 §5.3, the adversary's `~` coefficients) over the
μCMZ transcript basis: coefficients for `G₀`, `H`, `X₀`, `Xᵣ`, `X⃗`, and one
`(αᵤ, αᵥ)` pair per issued tag `(Uⱼ, Vⱼ)`. Tag coefficients are a list, so the type
is independent of the Sign-query count; `eval` `zipWith`s them against the issued
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
Honest instrumented oracles for secret key `sk`, crs `H`, and public parameters
`pp = (X₀, Xᵣ, X⃗)`. `sign` / `verify` delegate to `μCMZBaseMACSyntax F gen` (the
seam this game crosses); `help` destructures the concrete μCMZ `sk` directly for
`Z = (x₀+xᵣ)·A₀ + Σᵢ xᵢ·Aᵢ`.

- `sign` runs `.MAC` and appends `(m⃗, σ)` to the log;
- `verify` returns `.verify` iff the representations are transcript-consistent
  (else `false`);
- `help` answers the linear-form query using `sk` directly.
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
crs `H` and public parameters `(X₀, Xᵣ, X⃗)`, it queries the instrumented oracles
and outputs a forgery `(m⃗*, (U*, V*))` with representations of `U*` and `V*` over
the final transcript.
-/
structure AGMUFAdversary (F G : Type) (n : ℕ) where
  run : G → G × G × (Fin n → G) →
    OracleComp (AGMOracleSpec F G n)
      ((Fin n → F) × (G × G) × AGMRepr F n × AGMRepr F n)

/--
The AGM UF-CMVA(+Help) experiment for μCMZ (O24 Figure 5, instrumented per §5.3).
Setup and keygen delegate to `μCMZBaseMACSyntax F gen`; the adversary runs against
`agmOracleImpl`; returns `true` iff the forgery representations are transcript-
consistent, the forged message is fresh, and the forgery verifies.
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

/-- The AGM UF-CMVA(+Help) advantage `Pr[= true | AGM_UF_CMVAGame …]`, kept a
function of `secParam` so the (deferred) negligibility statement can quantify over
it. -/
noncomputable abbrev AGM_UF_CMVAAdv (A : AGMUFAdversary F G n) (secParam : ℕ) : ℝ≥0∞ :=
  Pr[= true | AGM_UF_CMVAGame (gen := gen) secParam A]

/-! ## Security statements (O24 §5.3)

The `n = 1` reduction's core (the `AGMRepr ↔ ReprCoeffs` eval bridge, the
mechanized identity-branch contradiction, the reduction adversary, and root
recovery) lives in `KVAC.Schemes.MicroCMZ.AGMReduction.Core`; the probability
bound and the security theorems `agm_ufcmva_le_n1` / `agm_ufcmva_le` are still
forthcoming. The reduction is split into its own file because it imports
`AGMPolynomial` — see the order-instance hazard note at `glog` above (the bridge
needs `glog`, but `glog`'s *proof* must elaborate without those instances in
scope).

The bridging lemma to the plain `UF_CMVAGame` of `KVAC.Core.AlgebraicMAC.Security`
is also deferred: it needs a runtime `WellBehaved` predicate and a
`project : AGMUFAdversary → UFAdversary` translation, both coupled to the
reduction. This branch delivers its prerequisite: both games cross the
`AlgebraicMACSyntax` seam at `μCMZBaseMACSyntax F gen` (setup/keygen/MAC/verify are
delegated to the interface value, not inlined). -/

end KVAC.Schemes.MicroCMZ
