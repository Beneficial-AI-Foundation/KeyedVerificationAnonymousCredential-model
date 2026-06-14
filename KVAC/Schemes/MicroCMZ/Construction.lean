/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Core.AlgebraicMAC
import KVAC.Core.Group
import VCVio

/-!
# μCMZ as an algebraic MAC — construction (O24 §5.1, Figure 9 "Base MAC")

The base MAC underlying the μCMZ keyed-verification credential of Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552,
§5.1 (Figure 9). We instantiate the abstract `AlgebraicMACSyntax ProbComp`
(`KVAC.Core.AlgebraicMAC`) with the four algorithms `(S, K, M, V)`, prove the
support-based `Correct` predicate, and bundle them into the paper-level
`AlgebraicMAC` object `microCMZMAC`.

Everything is stated over the abstract `SampleableGroup F G` from
`KVAC.Core.Group` — no concrete curve. Per the project layering, this file is a
"game-construction" file (it samples), so it uses the `SampleableGroup`
variable block (see `docs/STYLE_GUIDE.md`, *Prime-order group convention*).

## The construction (Figure 9, Base MAC)

- `S(1^λ, n)`: sample `H ←$ G`; `crs := (Γ, H)`. Here `Γ` (the group
  description) is the typeclass, so the CRS carries only `H : G`.
- `K(crs)`: sample `sk = (x₀, xᵣ, x⃗) ←$ Zₚ^{n+2}`;
  `pp = (X₀ = x₀·H, Xᵣ = xᵣ·G₀, Xᵢ = xᵢ·G₀)`.
- `M(sk, m⃗)`: sample `U` (see below); `V := (x₀ + xᵣ + Σᵢ mᵢxᵢ)·U`; return
  `σ = (U, V)`.
- `V(sk, m⃗, (U,V))`: return `U ≠ 0 ∧ V = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·U`.

## Nonzero `U` and perfect correctness

The paper writes `U ←$ G`, but the repo's `Correct` (in
`KVAC.Core.AlgebraicMAC.Correctness`) is *perfect* (support-based): every tag in
the support of `M` must verify. Since `V` rejects `U = 0` (O24 Figure 9,
footnote 5 — required for security, unlike CMZ14), the honest tag `(0, 0)` would
break perfect correctness. We therefore sample `U` uniformly from the *nonzero*
elements of `G` — in a prime-order group these are exactly the generators, the
standard MAC_GGM reading. Sampling the nonzero subtype `{g : G // g ≠ 0}`
directly (rather than `u·G₀` for a nonzero scalar `u`) makes `U ≠ 0`
definitional and avoids needing `NoZeroSMulDivisors F G`, which the abstract
`PrimeOrderGroup` does not provide.

## Cross-reference: Signal's `zkgroup` (non-normative)

The deployed Signal analogue is `rust/zkgroup/src/crypto/credentials.rs`
(`KeyPair::generate` / `credential_core`). It is a *different* MAC: a MAC_GGM
variant with group-element attributes `Mᵢ`, a standalone `W = w·G_w` term, a
per-credential system scalar `t`, and the public key packed as `C_W` / `I`, over
Ristretto255 — i.e. `V = W + (x₀ + x₁·t)·U + Σᵢ yᵢ·Mᵢ`. Per the project's
paper-driven layering that deployment is an *instance*, never the framework; this
file follows O24 Figure 9 (`V = (x₀ + xᵣ + Σᵢ mᵢxᵢ)·U`) with scalar attributes
over an abstract group. The pointer is for orientation only.

## Out of scope

- UF-CMVA security (O24 Theorem 5.1, AGM under 3-DL) — needs the AGM model, the
  3-DL assumption, and straight-line extraction, none of which exist yet.
- The full credential protocol (Issue / Present, the predicate `φ`, the ZK
  relations of Eqs. 9–11) — the rest of §5.1. In μCMZ, Issue uses *Pedersen*
  commitments (`C' = Σ mᵢXᵢ + sG`; unblind `V' − sU'`), not the ElGamal
  `D1/D2/E1/E2/S1/S2` path of the libsignal analogue.
-/

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core OracleComp

/--
Uniform sampling from the nonzero elements of a nontrivial finite group. The
subtype `{g : G // g ≠ 0}` is a nonempty `Fintype`, so it inherits a
`SampleableType` instance by transport from `Fin (Fintype.card _)`.
-/
noncomputable instance instSampleableTypeNeZero {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] [Nontrivial G] : SampleableType {g : G // g ≠ 0} :=
  haveI : Nonempty {g : G // g ≠ 0} := ⟨⟨_, (exists_ne (0 : G)).choose_spec⟩⟩
  haveI : NeZero (Fintype.card {g : G // g ≠ 0}) := ⟨Fintype.card_ne_zero⟩
  SampleableType.ofEquiv (Fintype.equivFin {g : G // g ≠ 0}).symm

/--
A fixed generator `G₀` of `G` (O24's `G ∈ Γ`). Used only to build the public
parameters `pp` in `keygen`; `verify` never reads `pp`, so the choice of
generator is irrelevant to correctness. Noncomputable — the abstract group
exposes no computable generator.
-/
noncomputable def generator (G : Type) [AddCommGroup G] [IsAddCyclic G] : G :=
  (IsAddCyclic.exists_generator (α := G)).choose

/--
μCMZ as a syntactic algebraic MAC (O24 §5.1, Figure 9 "Base MAC"), over the
abstract `SampleableGroup F G`. The field type `F` and group `G` are explicit
because they do not appear in the result type `AlgebraicMACSyntax ProbComp`
(the carrier families `Msg`, `Sk`, … are projected out of the structure value).
Noncomputable because it uses `generator`.

Carrier types:
- `Crs _ _ := G`            — holds `H` (the group description `Γ` is the typeclass);
- `Msg _   := F`            — attributes live in the scalar field;
- `Sk _    := F × F × (Fin n → F)`  — `(x₀, xᵣ, x⃗)`;
- `Pp _    := G × G × (Fin n → G)`  — `(X₀, Xᵣ, X⃗)`;
- `Tag _   := G × G`        — `(U, V)`.
-/
noncomputable def microCMZ (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [DecidableEq G] [SampleableGroup F G] :
    AlgebraicMACSyntax ProbComp where
  Crs := fun _ _ => G
  Msg := fun _ => F
  Sk := fun {_secParam n} _ => F × F × (Fin n → F)
  Pp := fun {_secParam n} _ => G × G × (Fin n → G)
  Tag := fun _ => G × G
  DecidableEqMsg := fun _ => inferInstance
  setup := fun _secParam _n => ($ᵗ G)
  keygen := fun {_secParam n} crs => do
    let x0 ← $ᵗ F
    let xr ← $ᵗ F
    let x ← $ᵗ (Fin n → F)
    pure ((x0, xr, x), (x0 • crs, xr • generator G, fun i => x i • generator G))
  MAC := fun {_secParam _n} _crs sk m => do
    let U ← ($ᵗ {g : G // g ≠ 0} : ProbComp {g : G // g ≠ 0})
    pure (U.val, (sk.1 + sk.2.1 + ∑ i, m i * sk.2.2 i) • U.val)
  verify := fun {_secParam _n} _crs sk m t =>
    decide (t.1 ≠ 0) && decide (t.2 = (sk.1 + sk.2.1 + ∑ i, m i * sk.2.2 i) • t.1)

/--
μCMZ satisfies perfect (support-based) correctness: every honestly produced tag
verifies. The MAC samples a nonzero `U`, so the `U ≠ 0` check passes; the
verification equation `V = (x₀ + xᵣ + Σᵢ mᵢxᵢ)·U` holds by construction (`rfl`),
since `MAC` builds `V` with exactly that scalar. (The paper writes `verify`'s
scalar as `Σᵢ xᵢmᵢ`; we use the commutatively-equal `Σᵢ mᵢxᵢ` so the two sides
are syntactically identical.)
-/
theorem microCMZ_correct (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [DecidableEq G] [SampleableGroup F G] :
    Correct (microCMZ F G) := by
  intro _secParam n crs _hcrs keys _hkeys m sig hsig
  obtain ⟨sk, _pp⟩ := keys
  simp only [microCMZ, support_bind, support_uniformSample, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hsig
  obtain ⟨U, _, rfl⟩ := hsig
  simp only [microCMZ, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  refine ⟨U.property, ?_⟩
  trivial

/--
The paper-level μCMZ algebraic MAC (O24 Definition 3.1): the syntactic scheme
paired with its correctness proof. Noncomputable (via `microCMZ`).
-/
noncomputable def microCMZMAC (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [DecidableEq G] [SampleableGroup F G] : AlgebraicMAC :=
  ⟨microCMZ F G, microCMZ_correct F G⟩

end KVAC.Schemes.MicroCMZ
