<!--
Source of truth for slides.html. Edit this file, then regenerate with:

    python3 build_slides.py

Conventions the builder understands:
  - Slides are separated by a line containing only `---`.
  - The first slide is the title slide: `#` is the title, `##` the subtitle,
    the remaining lines the footer (presenter, date).
  - On the other slides: `##` is the slide title; an image line
    `![alt](assets/x.png)` fills the left pane; a `**bold**` line
    immediately before a ```lean fence is that block's caption; `- ` lines
    become the explanatory bullets.
  - `figwidth: NN%` sets the width of the image pane (default 38%).
  - `codesize: N.Nvh` shrinks the slide's code font (default 1.5vh).
  - `figscale: X` (one global directive) multiplies every figure's size by
    X; figures keep the same relative scale, so legibility stays uniform.
  - `figzoom: X` (per slide) additionally zooms that slide's figure,
    deliberately departing from the uniform scale.
  - A bullet that BEGINS with a `backticked` fragment does not render as a
    bullet: it becomes a hover tooltip attached to that fragment's
    occurrences in the slide's code (dotted underline). If the fragment
    occurs nowhere in the code, the bullet stays visible.
  - Inline `backticks` become code; raw HTML such as <sup>λ</sup> passes
    through.
-->

<!-- figscale: 1.15 -->

# Formalizing KVAC in Lean

## The μCMZ case

Beneficial AI Foundation
July 30th, 2026

---

## Base MAC · the structure

<!-- figwidth: 50% -->
<!-- codesize: 1.2vh -->
![Base MAC panel](assets/basemac.png)

### Ambient context: the fixed group

```lean
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
```

### Abbreviations used in the carrier types

```lean
abbrev Key    (F : Type) (n : ℕ) : Type := F × F × (Fin n → F)
abbrev Params (G : Type) (n : ℕ) : Type := G × G × (Fin n → G)
abbrev Code   (G : Type)         : Type := G × G
```

### The carrier types (Crs, Msg, Sk, Pp, Tag) and the four procedures

```lean
noncomputable def μCMZBaseMACSyntax (gen : G) :
    AlgebraicMACSyntax ProbComp where
  Crs := fun _ _ => G                                    -- Crs : Nat → Nat → Type
  Msg := fun _ => F                                      -- Msg : {secParam n : Nat} → Crs secParam n → Type
  Sk  := fun {_secParam n} _ => Key F n                  -- Sk : {secParam n : Nat} → Crs secParam n → Type
  Pp  := fun {_secParam n} _ => Params G n               -- Pp : {secParam n : Nat} → Crs secParam n → Type
  Tag := fun _ => Code G                                 -- Tag : {secParam n : Nat} → Crs secParam n → Type
  DecidableEqMsg := fun _ => inferInstance               -- DecidableEqMsg : {secParam n : Nat} → 
                                                         --     (crs : Crs secParam n) → DecidableEq (Msg crs)
  setup  := setup                                        -- setup : (secParam n : Nat) → M (Crs secParam n)
  keygen := fun {_secParam _} crs => keygen crs gen      -- keygen : {secParam n : Nat} → 
                                                         --     (crs : Crs secParam n) → M (Sk crs × Pp crs)
  MAC    := fun {_secParam _} _ sk m => mac sk m         -- MAC : {secParam n : Nat} → 
                                                         --     (crs : Crs secParam n) → Sk crs → (Fin n → Msg crs) → 
                                                         --     M (Tag crs)
  verify := fun {_secParam _} _ sk m t => verify sk m t  -- verify : {secParam n : Nat} → (crs : Crs secParam n) → Sk crs →
                                                         --     (Fin n → Msg crs) → Tag crs → Bool
```
### The μCMZ MAC: an instance of the `AlgebraicMAC` structure (O24 Def 3.1)

```lean
noncomputable def μCMZBaseMAC (gen : G) : AlgebraicMAC :=
  ⟨μCMZBaseMACSyntax F gen, μCMZBaseMAC_correct F gen⟩
```

- `noncomputable`: we verify the output distribution, not run code. The flag itself comes from choice inside the generic sampler (`Fintype.equivFin`).
- `fun`: each carrier field is a type family indexed by secParam, n, and the crs (types in the comments). μCMZ's spaces depend only on n, so the lambdas bind n where needed and discard the rest.
- `μCMZBaseMAC`: Definition 3.1 admits a scheme only together with correctness, so the pair syntax + `μCMZBaseMAC_correct` is the certified scheme. μCMZ's correctness is perfect (support-based).

---

## Base MAC · µCMZ.S (setup)

<!-- figzoom: 1.4 -->

<!-- figwidth: 25% -->
<!-- codesize: 1.2vh -->
![Base MAC, procedure µCMZ.S](assets/cell_s.png)

### µCMZ.S · setup

```lean
noncomputable def setup {G : Type}
    [SampleableType G] (_secParam _n : ℕ) :
    ProbComp G :=
  $ᵗ G
```

- The formalization is per-group, not asymptotic: each theorem is an advantage inequality for one fixed group, e.g. Theorem 5.1's Adv<sup>ufcmva</sup>(A) ≤ Adv<sup>3-dl</sup>(B₁) + Adv<sup>dl</sup>(B₂) + 3/p. No λ, no GrGen sampling, no negligibility; at Ristretto255, 3/p ≈ 2<sup>−251</sup>.
- Line 1, Γ ← GrGen(1<sup>λ</sup>), has no runtime counterpart: the typeclass carries 𝔾 and p, the parameter `gen` carries G₀.
- `_secParam` and `_n` mirror S(1<sup>λ</sup>, n); nothing depends on them.
- `SampleableType`: VCV-io class of finite inhabited types with a canonical uniform selection (`selectElem : ProbComp β`, full support, all outputs equally likely); it is what the `$ᵗ` sampling notation runs on.
- `ProbComp`: VCV-io's monad of probabilistic computations (`OracleComp unifSpec`): programs with access to uniform sampling, whose semantics is the output distribution via `evalDist` (with `support` for the possible outputs).
- The crs reduces to H as a consequence of the per-group model: Γ is ambient (the typeclass plus `gen`), so sampling H is all that remains of setup; `keygen` receives H and `gen`, the paper's crs data.

---

## Base MAC · µCMZ.K (keygen)

<!-- figzoom: 1.4 -->

<!-- figwidth: 25% -->
<!-- codesize: 1.2vh -->
![Base MAC, procedure µCMZ.K](assets/cell_k.png)

### µCMZ.K · keygen

```lean
noncomputable def keygen {n : ℕ}
    (H : G) (gen : G) :
    ProbComp (Key F n × Params G n) := do
  let x₀ ← $ᵗ F
  let xᵣ ← $ᵗ F
  let x  ← $ᵗ (Fin n → F)
  let X₀ := x₀ • H
  let Xᵣ := xᵣ • gen
  let X  := fun i => x i • gen
  pure ((x₀, xᵣ, x), (X₀, Xᵣ, X))
```

- The single draw sk ←$ ℤ<sub>p</sub><sup>n+2</sup> is three draws: x₀, xᵣ, and the vector x; the joint distribution is the same.
- X₀ = x₀·H uses the CRS element H, while Xᵣ and X use `gen` (G₀), matching the two distinct bases in Base MAC.
- `ProbComp (Key F n × Params G n)`: the return type: a probabilistic computation producing sk : Key F n = (x₀, xᵣ, x) together with pp : Params G n = (X₀, Xᵣ, X), the paper's "return sk, pp".
- `H`: the crs: sampled once by `setup`, public, and with unknown discrete log relative to G₀. Basing X₀ = x₀·H on it makes pp perfectly binding to sk, which the statistical-anonymity proof uses (O24 §2.3.1).
- `pure`: the monad's return: embeds a value as a probabilistic computation that samples nothing (a point-mass distribution). All of keygen's randomness happens in the three draws above.
- `F`: the scalar field, the paper's ℤ<sub>q</sub> (the group order, written p elsewhere in the paper). The key is not one F: sk lives in `Key F n` = F × F × (Fin n → F) ≅ ℤ<sub>q</sub><sup>n+2</sup>, matching Base MAC's draw.
- `two distinct bases`: a base is a fixed group element others are written against: X = x·B, with x the discrete logarithm of X to base B. Base MAC uses two independent bases, H for X₀ and G₀ (`gen`) for Xᵣ and X; independent means no known discrete-log relation between them, which is what makes pp binding to sk.
- `do`: monadic sequencing notation, sugar for nested `bind`s in ProbComp. Inside it, `let x ← e` binds the result of a probabilistic step (here the draws), `let y := e` is an ordinary definition, and the block ends by returning a value with `pure`.

---

## Base MAC · µCMZ.M (mac)

<!-- figzoom: 1.75 -->

<!-- figwidth: 25% -->
<!-- codesize: 1.2vh -->
![Base MAC, procedure µCMZ.M](assets/cell_m.png)

### µCMZ.M · mac

```lean
noncomputable def mac {n : ℕ} (sk : Key F n)
    (m : Fin n → F) : ProbComp (Code G) := do
  let U ← uniformNonzero G
  pure (U, macScalar sk m • U)
```

### The shared scalar

```lean
def macScalar {n : ℕ} (sk : Key F n)
    (m : Fin n → F) : F :=
  let (x₀, xᵣ, x) := sk
  x₀ + xᵣ + ∑ i, x i * m i
```

- Base MAC writes U ←$ 𝔾, but the paper's defining MAC equation (Eq. 1, §5) samples U from the nonzero elements. Our formalization follows Eq. 1: `uniformNonzero G`.
- This removes the 1/p mass where the honest tag (0, 0) would fail verification, and gives perfect (support-based) correctness.
- The scalar `x₀ + xᵣ + Σᵢ xᵢ·mᵢ` is `macScalar`, shared verbatim with `verify`:  `mac` returns `(U, macScalar sk m • U)` and `verify` tests `V = macScalar sk m • U`.

---

## Base MAC · µCMZ.V (verify)

<!-- figzoom: 1.75 -->

<!-- figwidth: 25% -->
<!-- codesize: 1.2vh -->
![Base MAC, procedure µCMZ.V](assets/cell_v.png)

### µCMZ.V · verify

```lean
def verify {n : ℕ} (sk : Key F n)
    (m : Fin n → F) (t : Code G) : Bool :=
  let (U, V) := t
  decide (U ≠ 0) && decide (V = macScalar sk m • U)
```

- The mapping is 1-1: `decide` realizes the two checks as a Bool conjunction; deterministic, so no `ProbComp`.
- `U ≠ 0`: rejects the universal forgery (0, 0), which would verify for every message and key (V = s·0 holds for any s). The check defends the verifier from dishonest parties; honest issuance never trips it, since `mac` samples U nonzero. Implicit in CMZ14, made explicit in O24 (footnote 5).
- `decide`: the term-level `decide` function (a tactic of the same name exists): it evaluates a decidable proposition to a `Bool`, given a `Decidable` instance. Here `DecidableEq G` supplies the instances for U ≠ 0 and V = macScalar sk m • U.
