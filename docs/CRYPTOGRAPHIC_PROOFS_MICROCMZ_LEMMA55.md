# Cryptographic proofs of O24 Lemma 5.5 and Claims 5.6–5.7, with corrections to the paper

This document gives the cryptographic (pen-and-paper) proofs of Lemma 5.5 and
Claims 5.6 and 5.7 of Orrù, *Revisiting Keyed-Verification Anonymous
Credentials*, IACR ePrint 2024/1552 ("O24", as `docs/Orru_2024.pdf`),
correcting the printed proofs where they are wrong or incomplete.

Each departure from the paper is stated with its page reference — in Shared
conventions where it concerns the setting, in the Remarks at the end where it
concerns the proofs — and is checkable by hand against the paper.

It is not the Lean formalisation of these results: that is tracked by
the blueprint nodes `attribute_lifting`, `forgery_case_gap_dl` and
`forgery_case_mac` in `docs/KVACDocs/DocMicroCMZ.lean` and by item 6 of
`docs/MICROCMZ_REMAINING.md`.

The proofs here are intended as the reference for the Lean statements and
proofs of that item. Where they touch corrections already recorded in
`docs/presentations/rolf-status/errata.md` (items 1, 2 and 6, on the Lemma 5.4
bound and the Theorem 5.1 bound assembled from Lemma 5.5; item 5, on the sign of Claim 5.6's extraction; 
items 9–11, on Claim 5.6's `x_r` and Verify query) or in
`docs/DESIGN_ALTERNATIVES.md` (its two Claim 5.7 entries), they agree with them
and cite the item; corrections not in those documents are new here.

## Shared conventions

`Γ = (𝔾, p, G)` with `p` prime and `G` a generator of `𝔾`. Since `|𝔾| = p`:

> **(F1)** For `c ∈ ℤ_p`: `cG = 0_𝔾` iff `c = 0` in `ℤ_p`.  
> **(F2)** `ℤ_p` is a field, so `c·d ≠ 0` iff `c ≠ 0` and `d ≠ 0`; and every `c ≠ 0` is invertible.  
> **(F3)** If `L(w) = Σᵢ cᵢwᵢ` is a linear form with `c ≠ 0`, and `w` is uniform on `ℤ_pⁿ`, then `L(w)` is uniform on `ℤ_p`; in particular `Pr[L(w) = 0] = 1/p`.

**The `n`-attribute game.** `A` is the adversary against the `n`-attribute AGM UF-CMVA(+Help) game, `n = poly(λ)`, `n > 1`. The secret key is `(x₀, x_r, x₁,…,x_n)`, uniform on `ℤ_p^{n+2}`; the public parameters are `pp_n = (Γ, H, X₀, X_r, X₁,…,X_n)` with `X₀ = x₀H`, `X_r = x_rG`, `Xᵢ = xᵢG`. `H` is sampled by setup; nothing below depends on whether from `𝔾` (Figure 9) or `𝔾^×` (the change proposed in #149). A MAC on `m = (m₁,…,m_n)` is `(U, sU)` with

`s := x₀ + x_r + Σᵢ₌₁ⁿ mᵢxᵢ`, `U ←$ 𝔾^×`

and `Verify(m,(U,V))` accepts iff `U ≠ 0_𝔾` and `V = sU`. `A` makes `q` Sign queries `m₁,…,m_q` and outputs `(m*, (U*,V*))` with `m* ≠ m_j` for all `j`, without loss of generality, since an output with `m* ∈ {m₁,…,m_q}` loses.

**Sampling of `U`.** Figure 9's `µCMZ.M` (p. 34) samples `U ←$ 𝔾`; here, as in the Lean `mac`, `U ←$ 𝔾^×`: Verify rejects `U = 0_𝔾`, and Definition 3.1 (p. 25) requires every honest MAC to verify. Nothing below depends on which set `U` is drawn from — under `𝔾`, `Bgap` signs with `u ←$ ℤ_p`.

**Help oracle** (p. 38). `Help(A₀, Avec, Z)` returns `1` iff `Z = (x₀+x_r)A₀ + Σᵢ₌₁ⁿ xᵢAᵢ`, where `Avec = (A₁,…,A_n)`.

**Algebraic adversaries.** Representations are not oracle arguments. What the AGM adds is a condition on `A`: whenever it submits or outputs a group element `Y`, it also supplies a **representation** — a coefficient vector `ρ_Y` over the basis of elements it has seen, with `Y = Σ_b (ρ_Y)_b · b`.

**Representation checks.** In the paper's model representations are always correct. The Lean game (`AlgebraicMAC.lean`) instead lets `A` submit any representation, and Verify, Help and the win condition return 0 when one does not equal the element it is attached to. To match it, both reductions below first check every representation `A` supplies against the basis elements they hold, and return 0 when the check fails, as the Lean oracle does. The Lean simulator of Claim 5.6, `gapDlOracleImpl` in `AGMReduction/GapDLReduction.lean`, does exactly this for `Bgap`. For `B₁`'s relayed representations the 1-attribute challenger's check gives the same verdict as the real `n`-attribute oracle's, since `τ(ρ)` equals its element iff `ρ` does (Lemma 5.7.2).

**Statement.** `Adv^{ufcmva}_{µCMZ}(λ,n) ≤ Adv^{3-dl}_{GrGen}(λ) + Adv^{gapdl}_{GrGen}(λ) + 5/p`. The printed Lemmas 5.4 and 5.5 (pp. 36, 38) write `=`; `≤` is what a reduction proves and what Theorem 5.1 (p. 35) already states.

---

## The case split

Let `W` denote the event that `A` wins. Define

- **(i)** `Σᵢ₌₁ⁿ m*ᵢXᵢ = Σᵢ₌₁ⁿ m_{j,i}Xᵢ` for **some** `j ∈ [q]`;
- **(ii)** `Σᵢ₌₁ⁿ m*ᵢXᵢ ≠ Σᵢ₌₁ⁿ m_{j,i}Xᵢ` for **every** `j ∈ [q]`.

These are complementary, so exactly:

`Adv^{ufcmva}_{µCMZ}(λ,n) = Pr[W ∧ (i)] + Pr[W ∧ (ii)]`

Claim 5.6 bounds the first summand, Claim 5.7 the second. Both events are evaluated in the **real** `n`-attribute game.

---

# Claim 5.6 — case (i)

**Claim.** `Pr[W ∧ (i)] ≤ Adv^{gapdl}_{GrGen}(λ) + 1/p`.

**The gap-DL problem.** Given `(Γ, X)` with `X ←$ 𝔾`, find `x = log_G X`, with access to `DDH(A, Z)` returning `1` iff `Z = xA`.

## The reduction Bgap

`Bgap` receives `(Γ, X)` and the oracle `DDH`. It samples

`aᵢ, bᵢ ←$ ℤ_p (i ∈ [n])`, `z ←$ ℤ_p`, `x_r ←$ ℤ_p`, and `H` as the game samples it,

and sets

`Xᵢ := aᵢG + bᵢX (i ∈ [n])`, `X₀ := zH`, `X_r := x_r·G`.

It runs `A` on `pp_n = (Γ, H, X₀, X_r, X₁,…,X_n)`, checking the representations `A` supplies (see Representation checks) and otherwise ignoring them. `Bgap` is PPT whenever `A` is; at the end it takes the first `j ∈ [q]` satisfying `(i)`, found by testing each, `O(qn)` group operations.

So `Bgap` knows `x₀ = z` and `x_r`, and knows `aᵢ, bᵢ`, but not `x`. Writing `xᵢ = log_G Xᵢ = aᵢ + bᵢx`, the MAC scalar splits into a known part and an `x`-part:

> **(★)** `s = x₀ + x_r + Σᵢ mᵢxᵢ = (z + x_r + Σᵢ aᵢmᵢ) + (Σᵢ bᵢmᵢ)·x`

Write `d(m) := z + x_r + Σᵢ aᵢmᵢ` and `c(m) := Σᵢ bᵢmᵢ`, both computable by `Bgap`.

**Oracle simulation.**

|`A`'s query|`Bgap`'s reply|
|---|---|
|`Sign(m)`|`u ←$ ℤ_p^×`; return `(U := uG, V := d(m)·U + u·c(m)·X)`|
|`Verify(m,(U,V))`|if `c(m) = 0`: return `1` iff `U ≠ 0_𝔾` and `V = d(m)U`; else return `DDH(U, c(m)⁻¹(V − d(m)U))` and `U ≠ 0_𝔾`|
|`Help(A₀, Avec, Z)`|return `DDH(Σᵢ bᵢAᵢ, Z − (z + x_r)A₀ − Σᵢ aᵢAᵢ)`|

## Lemma 5.6.1 — the simulation is perfect

**Public parameters.** `aᵢ, bᵢ` uniform and independent give `Xᵢ = aᵢG + bᵢX` uniform on `𝔾` and independent across `i` (for fixed `X`, the map `(a,b) ↦ aG + bX` is `p`-to-one onto `𝔾`). `z` uniform gives `X₀ = zH` the real distribution (the real game computes `x₀H` with `x₀` uniform), `x_r` uniform gives `X_r` uniform. This matches the real game.

**Sign.** `U = uG` with `u ←$ ℤ_p^×` is uniform on `𝔾^×`, as in the game. By **(★)**,

`sU = [d(m) + c(m)x]·uG = d(m)·U + u·c(m)·(xG) = d(m)·U + u·c(m)·X`

which is exactly `V`. So the reply is the real MAC.

**Verify.** By **(★)**, `V = sU ⟺ V − d(m)U = c(m)·xU`. If `c(m) = 0` this reads `V = d(m)U`, checked directly. If `c(m) ≠ 0`, it is invertible by **(F2)** and the condition becomes `c(m)⁻¹(V − d(m)U) = xU`, which is exactly what `DDH` decides. The conjunct `U ≠ 0_𝔾` is checked separately in both branches.

**Help.** With `xᵢ = aᵢ + bᵢx`,

`(x₀+x_r)A₀ + Σᵢ xᵢAᵢ = (z+x_r)A₀ + Σᵢ aᵢAᵢ + x·(Σᵢ bᵢAᵢ)`

so `Z` satisfies the Help equation iff `Z − (z+x_r)A₀ − Σᵢ aᵢAᵢ = x·(Σᵢ bᵢAᵢ)`, which is what `DDH` decides. ∎

## Lemma 5.6.2 — `b` stays uniform given `A`'s view

**Notation.** `Δ := m_j − m*` is the vector `(Δ₁,…,Δ_n)` with `Δᵢ = m_{j,i} − m*ᵢ`. Since `m* ≠ m_j` means the two vectors differ in at least one coordinate, `Δ ≠ 0`.

**Hypothesis.** `Bgap` sampled `aᵢ, bᵢ ←$ ℤ_p` independently and published `Xᵢ = aᵢG + bᵢX`. `A` has run to completion against the simulated game.

**Conclusion.** Conditioned on `A`'s entire view, `b = (b₁,…,b_n)` is uniform on `ℤ_pⁿ`.

### Why it is needed

When case (i) holds, `Bgap` derives `(Σᵢ Δᵢaᵢ)·G = −(Σᵢ Δᵢbᵢ)·X` and recovers `x` by inverting `Σᵢ Δᵢbᵢ`. If that scalar is zero the equation reads `0 = 0` and `Bgap` learns nothing.

`Δ` is chosen by `A`: `m_j` is a Sign query and `m*` the forged message. So `A` selects the vector that multiplies `b`. If `A` knew `b`, it could force the sum to vanish — with `n = 2`, `b₂ ≠ 0` and `Δ = (b₂, −b₁)` the sum is `b₂b₁ − b₁b₂ = 0` — and then on runs where `A` wins in case (i), `Bgap` would extract nothing.

### Proof

**Step 1 — `Xᵢ` hides `bᵢ`.** Fix `i` and the value `w := log_G Xᵢ` that `A` sees. The pairs consistent with that observation are exactly those with `a + bx = w`, and for each `b ∈ ℤ_p` there is exactly one such `a`, namely `a = w − bx`. So all `p` values of `bᵢ` are equally consistent with `Xᵢ`. The `(aᵢ,bᵢ)` are sampled independently across `i`, so this holds jointly.

**Step 2 — nothing else leaks `b`.** `A`'s view is the public parameters, the oracle replies and its own coins. By Lemma 5.6.1 every reply equals the real `n`-attribute game's reply, and the real game computes replies from the key `(x₀, x_r, x₁,…,x_n)`, from `H`, and from the coins `u_j` it draws for Sign; it never sees `(aᵢ,bᵢ)` or `x`, and `H` and the `u_j` are drawn independently of them. So the replies depend on `b` only through the `xᵢ` already covered by Step 1.

Hence `b` is uniform on `ℤ_pⁿ` given `A`'s entire view. ∎

### Consequence

`Δ` is determined by `A`'s view; `b` is uniform given that view. Conditioning on the view therefore fixes `Δ` and leaves `b` fully random, so the two are independent and `Δ` may be treated as a constant while `b` ranges uniformly.

`Σᵢ Δᵢbᵢ` is then a linear form in `b` with coefficient vector `Δ ≠ 0`, evaluated at a uniform point of `ℤ_pⁿ`. A nonzero linear form takes each value of `ℤ_p` on exactly `pⁿ⁻¹` points, so

`Pr[Σᵢ Δᵢbᵢ = 0] = 1/p` exactly.

This is the sole source of the `1/p` in Claim 5.6. Note `b = 0` is not excluded — it is one of the `pⁿ` equally likely values and simply lies inside this `1/p`.

## Lemma 5.6.3 — on `(i)`, `Bgap` extracts `x`

Suppose `(i)` holds, and let `j` be its first witness. With `Δ` as in Lemma 5.6.2, `Δ ≠ 0`. Case (i) says

`Σᵢ m_{j,i}(aᵢG + bᵢX) = Σᵢ m*ᵢ(aᵢG + bᵢX)`

hence `(Σᵢ Δᵢaᵢ)G + (Σᵢ Δᵢbᵢ)X = 0_𝔾`, i.e.

> **(★★)** `(Σᵢ Δᵢaᵢ)·G = −(Σᵢ Δᵢbᵢ)·X`

If `Σᵢ Δᵢbᵢ ≠ 0` it is invertible by **(F2)**, and taking `log_G` of **(★★)** gives

`x = −(Σᵢ Δᵢaᵢ)·(Σᵢ Δᵢbᵢ)⁻¹`

which `Bgap` computes and returns. By Lemma 5.6.2 and **(F3)**, since `Δ` is determined by `A`'s view and `Δ ≠ 0`,

`Pr[Σᵢ Δᵢbᵢ = 0] = 1/p`. ∎

## Assembly of Claim 5.6

`Bgap`'s simulation is perfect (Lemma 5.6.1), so `Pr_real[W ∧ (i)] = Pr_sim[W ∧ (i)]`. Then

`Pr_sim[W ∧ (i)] ≤ Pr_sim[(i)] = Pr_sim[(i) ∧ Σᵢ Δᵢbᵢ ≠ 0] + Pr_sim[(i) ∧ Σᵢ Δᵢbᵢ = 0]`,

the inequality because `W ∧ (i) ⊆ (i)`, the equality a split on whether `Σᵢ Δᵢbᵢ = 0`. On `(i) ∧ Σᵢ Δᵢbᵢ ≠ 0`, `Bgap` outputs `x` (Lemma 5.6.3), whether or not `W` holds, so `Pr_sim[(i) ∧ Σᵢ Δᵢbᵢ ≠ 0] ≤ Adv^{gapdl}_{GrGen}(λ)`.

And `Pr_sim[(i) ∧ Σᵢ Δᵢbᵢ = 0] ≤ 1/p`: fix a view `v` of `A` in which `(i)` holds; `Δ` is then a fixed nonzero vector and `b` is uniform given `v` (Lemma 5.6.2), so by **(F3)** `Pr[Σᵢ Δᵢbᵢ = 0 | v] = 1/p`; averaging over such `v` gives `Pr_sim[(i) ∧ Σᵢ Δᵢbᵢ = 0] = Pr_sim[(i)]/p ≤ 1/p`.

Hence

`Pr[W ∧ (i)] ≤ Adv^{gapdl}_{GrGen}(λ) + 1/p` ∎

---

# Claim 5.7 — case (ii)

**Claim.** `Pr[W ∧ (ii)] ≤ Adv^{ufcmva}_{µCMZ}(λ,1) + 1/p`.

**The `1`-attribute game.** Key `(x₀, x_r, x₁)`, `pp₁ = (Γ, H, X₀, X_r, X₁)`. A MAC on `m′ ∈ ℤ_p` is `(U, s′U)` with `s′ := x₀ + x_r + m′x₁`; verification accepts iff `U ≠ 0_𝔾` and `V = s′U`. Its Help oracle has a one-entry vector: `Z = (x₀+x_r)A₀ + x₁A₁`.

**AGM bases.** After `q` Sign queries:

- `Bn = (G, H, X₀, X_r, X₁, X₂,…,X_n, U₁, V₁,…,U_q, V_q)`
- `B1 = (G, H, X₀, X_r, X₁, U₁, V₁,…,U_q, V_q)`

## The reduction B₁

`B₁` plays the `1`-attribute AGM UF-CMVA(+Help) game, receiving `pp₁`. **It knows none of `x₀, x_r, x₁`**, only group elements, so every reply to `A` must come from the challenger.

`B₁` samples `z₂,…,z_n ←$ ℤ_p`, sets `Xᵢ := zᵢX₁` for `i ∈ [2,n]`, and runs `A` on `pp_n = (Γ, H, X₀, X_r, X₁, X₂,…,X_n)`.

Define `μ(m) := m₁ + Σᵢ₌₂ⁿ zᵢmᵢ ∈ ℤ_p` and the linear map `τ : ℤ_p^{Bn} → ℤ_p^{B1}`

`τ(α_g, α_h, α₀, α_r, α₁, α₂,…,α_n, {α_{u,j}}, {α_{v,j}}) := (α_g, α_h, α₀, α_r, α₁ + Σᵢ₌₂ⁿ zᵢαᵢ, {α_{u,j}}, {α_{v,j}})`

`τ` rewrites a representation over `A`'s basis into one over the challenger's basis, which `B₁` needs because the challenger has never seen `X₂,…,X_n`. The two are different index sets: `τ` absorbs `α₂,…,α_n` into the `X₁` coordinate, since `B1` has no coordinate for `X₂,…,X_n`.

|`A`'s query|`B₁` forwards|
|---|---|
|`Sign(m)`|`Sign(μ(m))`; return the reply verbatim|
|`Verify(m,(U,V))`|`Verify(μ(m),(U,V))`; return the bit|
|`Help(A₀, Avec, Z)`|`Help(A₀, A′, Z)` where `A′ := A₁ + Σᵢ₌₂ⁿ zᵢAᵢ`|

**Representations.** `B₁` applies `τ` to each representation `A` supplies before relaying. For `A′`, which `A` never sent, `B₁` constructs `τ(ρ_{A₁} + Σᵢ₌₂ⁿ zᵢρ_{Aᵢ})` by linearity.

**Output.** `A` returns `(m*, (U*,V*))` with `ρ_{U*}, ρ_{V*}`; `B₁` returns `(μ(m*), (U*,V*))` with `τ(ρ_{U*}), τ(ρ_{V*})`.

`B₁` is PPT whenever `A` is: `n−1` scalar multiplications at setup, `O(n + q)` operations per query.

## Lemma 5.7.1 — the two scalars coincide

_For every `m ∈ ℤ_pⁿ`, `s = x₀ + x_r + Σᵢ₌₁ⁿ mᵢxᵢ` equals `s′ = x₀ + x_r + μ(m)x₁`._

`Xᵢ = zᵢX₁` gives `xᵢ = zᵢx₁` for `i ∈ [2,n]`, hence

`Σᵢ₌₁ⁿ mᵢxᵢ = m₁x₁ + Σᵢ₌₂ⁿ mᵢzᵢx₁ = (m₁ + Σᵢ₌₂ⁿ zᵢmᵢ)x₁ = μ(m)x₁`

Adding `x₀ + x_r` gives `s = s′`. ∎

## Lemma 5.7.2 — `τ` preserves the represented element

_If `ρ ∈ ℤ_p^{Bn}` represents `Y ∈ 𝔾`, then `τ(ρ)` represents the same `Y`._

The bases share every element except that `Bn` additionally contains `X₂,…,X_n`. On shared coordinates `τ` copies the coefficients, so those contributions are equal term by term. For the rest:

`α₁X₁ + α₂X₂ + ⋯ + α_nX_n = α₁X₁ + α₂z₂X₁ + ⋯ + α_nz_nX₁ = (α₁ + Σᵢ₌₂ⁿ zᵢαᵢ)X₁`

which is the `X₁` contribution of `τ(ρ)`. In particular the `U_j, V_j` coefficients are copied unchanged, because `U_j` and `V_j` are literally the same group elements in both bases — `B₁` relays the challenger's MACs unmodified. The same equality gives the converse: `ρ` equals a submitted element iff `τ(ρ)` does. ∎

## Lemma 5.7.3 — every simulated reply is the real one

**Sign.** The challenger returns `(U, s′U)` with `s′ = x₀ + x_r + μ(m)x₁`. By Lemma 5.7.1, `s′ = s`, so `(U, s′U) = (U, sU)` — what the `n`-attribute oracle returns on `m`. The distribution of `U` is the challenger's, hence the real one.

**Verify.** The `n`-attribute oracle accepts iff `U ≠ 0_𝔾` and `V = sU`; the `1`-attribute oracle at `μ(m)` iff `U ≠ 0_𝔾` and `V = s′U`. Identical by Lemma 5.7.1. The relayed representations are valid over `B1` by Lemma 5.7.2.

**Help.** By the computation in Lemma 5.7.1, `Σᵢ₌₁ⁿ xᵢAᵢ = x₁A₁ + Σᵢ₌₂ⁿ zᵢx₁Aᵢ = x₁·A′`, so

`Z = (x₀+x_r)A₀ + Σᵢ xᵢAᵢ ⟺ Z = (x₀+x_r)A₀ + x₁A′`

and the two oracles return the same bit. ∎

## Lemma 5.7.4 — the simulation is faithful exactly when `x₁ ≠ 0`

**(a)** Conditioned on `x₁ ≠ 0`, the pair (key, `A`'s view) in the simulation is identically distributed to the real one conditioned on `x₁ ≠ 0`. Indeed `x₀, x_r, x₁` come from the challenger and are uniform and independent, as in the real game. Fix `x₁ ≠ 0`; by **(F2)** the map `z ↦ zx₁` is a bijection of `ℤ_p`, so with `z₂,…,z_n` uniform and independent, `(x₂,…,x_n) = (z₂x₁,…,z_nx₁)` is uniform on `ℤ_pⁿ⁻¹` and independent of `(x₀,x_r,x₁)` — the real distribution. Replies agree by Lemma 5.7.3.

**(b)** Conditioned on `x₁ = 0` it is not: the simulation forces `xᵢ = zᵢ·0 = 0` for every `i ≥ 2`, so `s = x₀ + x_r` no longer depends on the message, whereas the real game leaves `x₂,…,x_n` uniform and the message still matters. This is not a claim that `A` cannot win on this branch — it is that the two experiments differ there, so this branch is bounded by `Pr[x₁ = 0]` instead of through the simulation. It is the only failure event, and `Pr[x₁ = 0] = 1/p`. ∎

## Lemma 5.7.5 — on `(ii)`, `B₁`'s output wins

**Validity.** `A`'s forgery verifies, so `U* ≠ 0_𝔾` and `V* = sU*`. By Lemma 5.7.1, `s = s′`, so `(U*,V*)` verifies for `μ(m*)` in the `1`-attribute game; representations are valid by Lemma 5.7.2.

**Freshness.** Using `Xᵢ = zᵢX₁` and `X₁ = x₁G`,

`Σᵢ m*ᵢXᵢ − Σᵢ m_{j,i}Xᵢ = (μ(m*) − μ(m_j))·x₁·G`

By **(F1)** this is `≠ 0_𝔾` iff `(μ(m*) − μ(m_j))·x₁ ≠ 0`, and by **(F2)** iff both `μ(m*) ≠ μ(m_j)` and `x₁ ≠ 0`. So `(ii)` gives `μ(m*) ≠ μ(m_j)` for every `j`. `B₁`'s Sign queries were exactly `μ(m₁),…,μ(m_q)`, so `μ(m*)` was never queried. ∎

## Assembly of Claim 5.7

Splitting on `x₁` is exact:

`Pr_real[W ∧ (ii)] = Pr_real[W ∧ (ii) ∧ x₁ ≠ 0] + Pr_real[W ∧ (ii) ∧ x₁ = 0]`

**Second term.** `≤ Pr[x₁ = 0] = 1/p`. This term exists because the simulation is faithful only when `x₁ ≠ 0` (Lemma 5.7.4), while in the real game `(ii)` can hold with `x₁ = 0`: take `n = 2`, `x₁ = 0`, `x₂ ≠ 0`, `m* = (0,1)`, `m_j = (0,0)`; then `Σᵢ m*ᵢXᵢ = X₂ ≠ 0_𝔾 = Σᵢ m_{j,i}Xᵢ`. So the `x₁ = 0` part of `W ∧ (ii)` is counted on its own, at most `Pr[x₁ = 0]`. Whether `1/p` is tight is not claimed.

**First term.** `x₁` is uniform in both experiments, so `Pr[x₁ ≠ 0] = 1 − 1/p` in each. By Lemma 5.7.4(a) the conditional distributions agree, so

`Pr_real[W ∧ (ii) ∧ x₁ ≠ 0] = Pr_sim[W ∧ (ii) ∧ x₁ ≠ 0]`

an equality, not a bound. By Lemma 5.7.5 that is at most `Adv^{ufcmva}_{µCMZ}(λ,1)`. Hence

`Pr[W ∧ (ii)] ≤ Adv^{ufcmva}_{µCMZ}(λ,1) + 1/p` ∎

---

# Assembly of Lemma 5.5

Combining the two claims with the exact case split:

`Adv^{ufcmva}_{µCMZ}(λ,n) = Pr[W ∧ (i)] + Pr[W ∧ (ii)] ≤ Adv^{gapdl}_{GrGen}(λ) + Adv^{ufcmva}_{µCMZ}(λ,1) + 2/p`

By Lemma 5.4 (corrected: `errata.md` items 1 and 2 — the printed `1/p` is `3/p`, and the printed `Adv^{dl}` summand, which no reduction produces, is dropped; this is the bound the Lean statement `agm_ufcmva_le_n1_explicit` in `AGMReduction/SecurityN1.lean` carries, proof pending), `Adv^{ufcmva}_{µCMZ}(λ,1) ≤ Adv^{3-dl}_{GrGen}(λ) + 3/p`. Therefore

`Adv^{ufcmva}_{µCMZ}(λ,n) ≤ Adv^{3-dl}_{GrGen}(λ) + Adv^{gapdl}_{GrGen}(λ) + 5/p` ∎

---

# Remarks

**`x_r` is omitted throughout the printed proofs.** Claim 5.7 gives `A` the parameters `(X₀, X₁,…,X_n)` with no `X_r` (p. 39), and its displayed verification equation has no `x_r` term (p. 40). Claim 5.6 lists `X_r` in `pp` but never defines it, and omits it from the Sign, Verify and Help formulas (p. 39). The repair used above — `Bgap` samples `x_r` itself and `B₁` forwards the challenger's `X_r` — is the natural one in each case, and costs nothing. The Claim 5.6 half is `errata.md` item 9; the Claim 5.7 half is not yet recorded.

**Claim 5.6's Verify formula is wrong as printed.** The paper (p. 39) gives `DDH(U, (Σᵢ bᵢmᵢ)⁻¹V − zU)`. Expanding with `V = d(m)U + c(m)xU` shows this equals `xU` only if `c(m)⁻¹d(m) = z`, which does not hold in general. The correct argument is `c(m)⁻¹(V − d(m)U)`, i.e. the inverse must multiply the whole difference, and `d(m)` must carry both `x_r` and `Σᵢ aᵢmᵢ`. The paper's simulated Verify in Claim 5.6 (p. 39) also omits the `U ≠ 0_𝔾` check that the real Verify (Figure 9) makes, in both branches: on `Verify(m,(0_𝔾,0_𝔾))` with `c(m) = 0` it answers 1, the real oracle 0. `Bgap`'s Verify row in the Oracle simulation table restores the check. Recorded as `errata.md` items 10 (the dropped `Σᵢ aᵢmᵢ`) and 11 (the misplaced inverse); those items write `c` for our `d(m)` and `d` for our `c(m)`. The Lean `gapDlOracleImpl` queries `DDH(c(m)·U, V − d(m)U)` instead, which avoids the inverse and covers the `c(m) = 0` branch, and checks `U ≠ 0_𝔾`.

**Claim 5.6 has a sign error and a dropped index.** From case (i) one gets `(Σᵢ Δᵢaᵢ)G = −(Σᵢ Δᵢbᵢ)X`, with a minus sign the paper omits (p. 39); consequently the extracted value is `x = −(Σᵢ Δᵢaᵢ)(Σᵢ Δᵢbᵢ)⁻¹`. The paper also writes `m*` for `m*ᵢ` inside both sums. The Sign reply in the same Claim (p. 39) writes the signed message as `m_{j,i}` in its first sum and as `mᵢ` in its second; both should read `m_{j,i}`, the `j`-th query. The sign is `errata.md` item 5; the index slips are proposed as item 20 in #217.

**Both claims state their failure probability backwards.** (p. 39) Claim 5.6: _"The equation is non-trivial with overwhelming probability 1/p"_ — it is non-trivial with probability `1 − 1/p`. Claim 5.7: _"Assuming X₁ ≠ 0_G (which happens with probability 1/p)"_ — `Pr[X₁ ≠ 0_𝔾] = 1 − 1/p`.

**`x₁ ≠ 0` appears twice in Claim 5.7, in different roles.** In Lemma 5.7.4 it is a hypothesis: the simulated distribution is correct only under it, and it is paid for at `1/p`. In Lemma 5.7.5 it is only a by-product of the freshness computation and is not needed there: `μ(m*) ≠ μ(m_j)` follows from `(ii)` alone.

**The `1/p` of each claim is exact.** `Pr[Σᵢ Δᵢbᵢ = 0] = 1/p` (Claim 5.6) and `Pr[x₁ = 0] = 1/p` (Claim 5.7) are exact probabilities, so the `1/p → 3/p` correction of Lemma 5.4 (`errata.md` item 1) does not apply to them.

**On `Pr_sim[W ∧ (ii) ∧ x₁ ≠ 0]`.** The conjunct `x₁ ≠ 0` is redundant on the simulated side for `q ≥ 1`, since `(ii)` already implies it there. It is written explicitly because the same expression appears on the real side of the equality, and there `(ii)` does _not_ imply `x₁ ≠ 0` — the counterexample shows it. The conjunct is what makes the two sides comparable.

**Collisions under `μ` are harmless.** Distinct `m_j ≠ m_k` may satisfy `μ(m_j) = μ(m_k)`, so `B₁` may submit the same scalar to `Sign` twice. Nothing in the UF-CMVA game (Figure 5, p. 25) forbids this: the game places no constraint on which messages the adversary queries, and the winning condition is that the forged message is _not in_ the query set — a set, so a repeat leaves it unchanged. The only effect is that `B₁`'s query set may be smaller than `q`, which makes freshness easier, and Lemma 5.7.5 establishes `μ(m*) ∉ {μ(m₁),…,μ(m_q)}` regardless.

**The AGM translation is load-bearing in Claim 5.7 and unnecessary in Claim 5.6.** `B₁` plays another AGM game, so it must itself be algebraic and supply representations over `B1`; Lemma 5.4's proof runs a monomial analysis directly on those coefficients, so without `τ`, `B₁` would not be an algebraic adversary of the 1-attribute game and `Adv^{ufcmva}(λ,1)` would not apply to it (in the Lean game, see Representation checks, the untranslated representation is simply rejected). `Bgap` plays gap-DL, which has no representation requirement, so it simply discards what `A` supplies. The paper omits `τ` at all three sites in Claim 5.7 (pp. 39–40) — Verify, Help, and the forgery. This point is already recorded in `docs/DESIGN_ALTERNATIVES.md`, entry "Claim 5.7: the `n → 1` collapse translates representations, not only messages", and `τ`, `μ` and `B₁` are already defined in Lean (`AGMReduction/AttributeCollapse.lean`: `collapseRepr`, `collapseMsg`, `nTo1Adversary`; no theorems yet).

**The Lean reduction also randomises `X₁`.** The paper (p. 39) and this document keep the challenger's `X₁` and set `Xᵢ := zᵢX₁` for `i ≥ 2` only. The Lean reduction `microCMZN3DLReduction` samples `r⃗ ←$ ℤ_pⁿ` and runs `nTo1Adversary`, which sets `Xᵢ := rᵢX₁` for every `i`, `X₁` included (`docs/DESIGN_ALTERNATIVES.md`, "Claim 5.7: the collapse direction is uniform in all `n` coordinates"). Claim 5.7 goes through unchanged with `μ(m) := Σᵢ rᵢmᵢ` and `τ`'s `X₁`-coordinate `Σᵢ rᵢαᵢ`; the failure event is still `x₁ = 0`, at `1/p`.

**The printed bound elides the gap-DL term.** Lemma 5.5 and Theorem 5.1 (pp. 38, 35) state `Adv^{3-dl} + Adv^{dl} + 3/p`. The final computation in the paper's proof of Lemma 5.5 (p. 39) first obtains `Adv(λ,1) + Adv^{gapdl} + 2/p` from Claims 5.6 and 5.7, then substitutes Lemma 5.4 and, in its last line, drops `Adv^{gapdl}` while keeping Lemma 5.4's `Adv^{dl}` (`errata.md` item 6). Since `Adv^{dl} ≤ Adv^{gapdl}` (a DL solver is a gap-DL solver that ignores its oracle), writing `dl` understates the assumption and makes the claimed bound smaller than what is proved. No `Adv^{dl}` term arises anywhere in Lemma 5.4's proof either, so the printed summand has no reduction behind it (`errata.md` item 2).

**Where the `5/p` comes from.** `3/p` from Lemma 5.4 (corrected from the printed `1/p` (pp. 36, 38), `errata.md` item 1), `1/p` from `Σᵢ Δᵢbᵢ = 0` in Claim 5.6, `1/p` from `x₁ = 0` in Claim 5.7 — the decomposition of `errata.md` item 6.

**Two inferences marked as such.** The paper writes `Σᵢ` without limits in the Help definition (pp. 35, 38); I read the sum as `i = 1..n`, since `Avec` has `n` entries. For `n = 1`, Eq. (15) (p. 38) gives every Help query representations of `A₀`, `A₁`, `Z`; the proof of Lemma 5.5 says nothing about them for general `n`, and I take the same requirement, since Help exists only inside the AGM game.
