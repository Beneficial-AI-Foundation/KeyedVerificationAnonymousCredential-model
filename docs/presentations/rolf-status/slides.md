<!--
Source of truth for slides.html. Edit this file, then regenerate with:

    python3 build_slides.py

Conventions the builder understands:
  - Slides are separated by a line containing only `---`.
  - The first slide is the title slide: `#` is the title, `##` the subtitle,
    the remaining lines the footer (presenter, date).
  - On the other slides: `##` is the slide title; the first image line
    `![alt](assets/x.png)` fills the left pane; later image lines render
    in-flow in the code column (e.g. paper equations above their Lean); an
    optional "title" on an in-column image, `![alt](path "#0d9488")`, draws
    an accent bar in that color (to visually pair the equation with its
    marked site in the panel figure); a `**bold**` line
    immediately before a ```lean fence is that block's caption; `- ` lines
    become the explanatory bullets.
  - `figwidth: NN%` sets the width of the image pane (default 38%).
  - `codesize: N.Nvh` shrinks the slide's code font (default 1.5vh).
  - `figscale: X` (one global directive) multiplies every figure's size by
    X; figures keep the same relative scale, so legibility stays uniform.
  - `figzoom: X` (per slide) additionally zooms that slide's figure,
    deliberately departing from the uniform scale.
  - An indented `  - ` line renders as a subbullet of the preceding bullet.
  - A `> ` line renders as a fine-print note (smaller font) in the bullet
    list.
  - Plain prose lines (matching none of the above) render in-flow in the
    code column as a text block, line breaks preserved (used for
    mathematical statements).
  - A bullet that BEGINS with a `backticked` fragment does not render as a
    bullet: it becomes a hover tooltip attached to that fragment's
    occurrences in the slide's code and text blocks (dotted underline);
    failing that, in the visible bullets. If the fragment occurs nowhere,
    the bullet stays visible.
  - Inline `backticks` become code; raw HTML such as <sup>λ</sup> passes
    through.
-->

<!-- figscale: 1.15 -->
<!-- figwidth: 200% -->
![Beneficial AI Foundation](assets/team-lockup/png/baif-agent-team-black.png)

# Formalizing Keyed-Verification Anonymous Credentials in Lean

## The μCMZ credential system

July 30th, 2026

---

## The μCMZ credential system

![The μCMZ protocol, three boxes](assets/fig9.png)

- <a href="#3">**Base MAC**</a> — the algebraic MAC underneath (slides 3–7). Construction and perfect correctness machine-checked.
- <a href="#8">**Credential Issuance**</a> — blind issuance of a tag on committed attributes (slides 8–11). The box's proof relations and Σ-protocols machine-checked; the protocol flow in progress.
- **Credential Presentation** — anonymous showing under a policy φ. Its proof relation R<sub>p</sub> (Eq. 11) is machine-checked; the rest is sequenced after Issuance.

---

## Base MAC · the structure

<!-- figwidth: 50% -->
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
  Crs := fun _ _ => G
  Msg := fun _ => F
  Sk  := fun {_secParam n} _ => Key F n
  Pp  := fun {_secParam n} _ => Params G n
  Tag := fun _ => Code G
  DecidableEqMsg := fun _ => inferInstance
  setup  := setup
  keygen := fun {_secParam _} crs => keygen crs gen
  MAC    := fun {_secParam _} _ sk m => mac sk m
  verify := fun {_secParam _} _ sk m t => verify sk m t
```
### The μCMZ MAC: an instance of the `AlgebraicMAC` structure (O24 Def 3.1)

```lean
noncomputable def μCMZBaseMAC (gen : G) : AlgebraicMAC :=
  ⟨μCMZBaseMACSyntax F gen, μCMZBaseMAC_correct F gen⟩
```

- `Crs`: interface type `Crs : Nat → Nat → Type` — the crs family, indexed by secParam and n.
- `Msg`: interface type `Msg : {secParam n : Nat} → Crs secParam n → Type` — the attribute space, selected by the crs.
- `Sk`: interface type `Sk : {secParam n : Nat} → Crs secParam n → Type` — the secret-key space.
- `Pp`: interface type `Pp : {secParam n : Nat} → Crs secParam n → Type` — the public-parameter space.
- `Tag`: interface type `Tag : {secParam n : Nat} → Crs secParam n → Type` — the tag space.
- `DecidableEqMsg`: interface type `{secParam n : Nat} → (crs : Crs secParam n) → DecidableEq (Msg crs)` — the UF-CMVA challenger computes the freshness check, so message equality must be decidable.
- `setup`: interface type `(secParam n : Nat) → M (Crs secParam n)`.
- `keygen`: interface type `{secParam n : Nat} → (crs : Crs secParam n) → M (Sk crs × Pp crs)`.
- `MAC`: interface type `{secParam n : Nat} → (crs : Crs secParam n) → Sk crs → (Fin n → Msg crs) → M (Tag crs)`.
- `verify`: interface type `{secParam n : Nat} → (crs : Crs secParam n) → Sk crs → (Fin n → Msg crs) → Tag crs → Bool`.
- `noncomputable`: we verify the output distribution, not run code. The flag itself comes from choice inside the generic sampler (`Fintype.equivFin`).
- `fun`: each carrier field is a type family indexed by secParam, n, and the crs (types in the comments). μCMZ's spaces depend only on n, so the lambdas bind n where needed and discard the rest.
- `μCMZBaseMAC`: Definition 3.1 admits a scheme only together with correctness, so the pair syntax + `μCMZBaseMAC_correct` is the certified scheme. μCMZ's correctness is perfect (support-based).

---

## Base MAC · µCMZ.S (setup)

<!-- figzoom: 1.4 -->

<!-- figwidth: 25% -->
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

---

## Credential Issuance · R<sub>iu</sub> relation

<!-- figzoom: 0.85 -->
![Credential Issuance panel, πᵢᵤ sites marked](assets/cell_iss_iu.png)

### R<sub>iu</sub> — the user's proof: opening of C′, policy φ

![O24 Equation 9](assets/eq9.png "#0d9488")

```lean
def riuRel (gen : G) : RiuStmt G F n → RiuWitness F n → Bool :=
  fun ⟨Cp, X, φ⟩ ⟨m, s⟩ => decide (Cp = (∑ i, m i • X i) + s • gen) && φ m
```

- `witness (m, s)`: the secret data whose knowledge the proof demonstrates: the attribute vector m and the blinding scalar s of the commitment C′ = Σᵢ mᵢ•Xᵢ + s•gen. In Lean, `RiuWitness F n` = (Fin n → F) × F. The statement (C′, X, φ) is public; the witness stays with the user, and HVZK guarantees the proof reveals nothing about it.
- `commitment C′`: a Pedersen commitment to the attributes, C′ = Σᵢ mᵢ•Xᵢ + s•gen: perfectly hiding (the uniform s masks m) and computationally binding under discrete log. (m, s) is its opening; R<sub>iu</sub> proves knowledge of an opening that satisfies φ, and the server later shifts it homomorphically to C″ = C′ + Xᵣ.
- **R<sub>iu</sub> in the box.** The boxed π<sub>iu</sub> of the panel: the user proves R<sub>iu</sub> (ZKP<sub>cmz.iu</sub>.P) with witness (m, s) when sending the commitment C′; the server checks it before issuing.
  - The frame around π<sub>iu</sub> marks the lines deleted in the anonymous-token variant µCMZ<sub>AT</sub> (one-more unforgeability, Theorem 5.3 — to be presented at a later time).

---

## Credential Issuance · R<sub>is</sub> relation

<!-- figzoom: 0.85 -->
![Credential Issuance panel, πᵢₛ sites marked](assets/cell_iss_is.png)

### R<sub>is</sub> — the server's proof: (U′, V′) well-formed under (x₀, u)

![O24 Equation 10](assets/eq10.png "#7c3aed")

```lean
def risRel (gen H : G) : RisStmt G → RisWitness F → Bool :=
  fun ⟨X₀, C'', U', V'⟩ ⟨x₀, u⟩ => decide
    (U' = u • gen ∧ X₀ = x₀ • H ∧
      V' = x₀ • U' + u • C'')
```

- **R<sub>is</sub> in the box.** The proof π<sub>is</sub> on the return leg: the server proves R<sub>is</sub> with witness (x₀, u) when sending (U′, V′); the user checks it, with C″ = C′ + Xᵣ recomputed locally, before unblinding.

---

## Credential Issuance · Special Soundness

<!-- figzoom: 0.6 -->
![Credential Issuance panel](assets/cell_iss.png)

### The explicit extractor (from `riuSigma`)

```lean
extract c₁ z₁ c₂ z₂ :=
  pure (fun i => (z₁.1 i - z₂.1 i) * (c₁ - c₂)⁻¹,
    (z₁.2 - z₂.2) * (c₁ - c₂)⁻¹)
```

### VCV-io's perfect special soundness (`SigmaProtocol.lean`)

```lean
def SpeciallySoundAt (σ : SigmaProtocol S W PC SC Ω P p) (x : S) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (σ.extract ω₁ p₁ ω₂ p₂), p x w = true
```

### Our theorem: special soundness with policy enforcement

```lean
theorem riuSigma_speciallySoundAt (gen : G) (Cp : G) (X : PublicBases G n)
    (φ : Policy F n)
    (hφ : Enforces (riuSigma (F := F) (n := n) gen) (Cp, X, φ)
            (fun ⟨m, _s⟩ => φ m)) :
    SpeciallySoundAt (riuSigma (F := F) (n := n) gen) (Cp, X, φ)
```

- VCV-io's `SpeciallySoundAt` implements the textbook definition of perfect special soundness: two accepting transcripts with the same announcement and distinct challenges yield, through the extractor, a witness for the relation. 
- At R<sub>iu</sub> the witness is an opening (m, s) of C′ satisfying φ; dually, `risSigma_speciallySound` recovers (x₀, u).
- Why perfect: the <a href="#4">per-group</a> formalization has no λ, so the computational notion (extraction fails with probability negligible in λ; DG23, Definition 4.6) is not expressible. The perfect notion holds by pure algebra: the extractor computes the witness by field arithmetic from any two such transcripts, with no hardness assumption.
<!-- - This is the knowledge-soundness seed of the box: Theorem 5.2's extractability bound rests on extracting exactly these witnesses. -->
- `Enforces`: φ-enforcement is a hypothesis, discharged today for `trivialPolicy` (`riu_enforces_trivialPolicy`); a verifier that checks φ in zero knowledge discharges it for a proper φ.
- `announcement`: the Σ-protocol's first message, sent by the prover before the challenge is drawn. Classically called the commitment; renamed here to avoid a clash with the commitment C′. In `SpeciallySoundAt` it is the variable pc, shared by both transcripts.
- `challenges`: the challenge is the verifier's message, a scalar drawn uniformly from F after the announcement is fixed. Two accepting responses to distinct challenges ω₁ ≠ ω₂ make (c₁ − c₂)⁻¹ in the extractor well defined.

---

## Credential Issuance · status

<!-- figzoom: 0.85 -->
![Credential Issuance panel, both proof sites marked](assets/cell_iss_annot.png)

- **Formalized (merged).** Both proof relations of the box and their interactive Σ-protocols (`riuSigma`, `risSigma`): perfect completeness, special soundness, and HVZK via explicit simulated transcripts; the policy layer (`Policy`, `trivialPolicy`).
- `HVZK`: honest-verifier zero-knowledge: a simulator given only the statement produces transcripts distributed identically to real interactions with the honest verifier, so the proof reveals nothing beyond the statement's validity. The Prop is VCV-io's `HVZK`, reused like `SpeciallySoundAt`; our simulators (`riuSimTranscript`, `risSimTranscript`) sample the response first and solve for the announcement.
- **Missing.** The flow itself (blinding s, C′ → C″ → (U′, V′), unblinding U := r·U′, V := r(V′ − s·U′)) — it instantiates the abstract KVAC syntax of Definition 4.2, in review (PR #77); Fiat–Shamir compilation of the Σ-protocols into the non-interactive π<sub>iu</sub>, π<sub>is</sub>; credential-level correctness (Definition 4.3).
