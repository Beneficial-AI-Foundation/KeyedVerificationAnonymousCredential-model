/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.Construction
import KVAC.Preliminaries.AnonymousTokens

/-!
# μCMZ_AT core — the anonymous-token variant of μCMZ (O24 §5.6, Figure 9)

The anonymous-token variant `μCMZ_AT` of the μCMZ scheme of Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint
2024/1552 (O24), instantiating the abstract `ATSyntax ProbComp`
(`KVAC.Preliminaries.AnonymousTokens`). Setup, key generation, and
verification are shared *definitionally* with the base MAC
(`KVAC.Schemes.MicroCMZ.Construction`); this file adds the blind
issuance protocol of Figure 9 and proves the support-based `Correct`
predicate, bundling both as the `AnonymousToken` object `μCMZATCore`
(syntax and correctness only — see that definition's docstring).

## Deviation from the printed Figure 9 — the π_is-less **core**

Figure 9's caption boxes only the *user's* issuance proof `π_iu` as the
part removable for anonymous tokens, so the printed `μCMZ_AT` server
still sends its issuance proof `π_is`. This file removes **both**
proofs, because the π_is-less scheme is the one the Theorem 5.11 proof
actually analyzes: its Sign oracle answers with the bare `(U', V')` and
its one-more unforgeability bound carries no zero-knowledge term (a
reduction holding no secret key cannot produce real `π_is` proofs). The
name `μCMZATCore` records this honestly. The π_is-carrying variant and
the lifting lemma — schematically
`OMUF(π_is scheme) ≤ OMUF(core) + Adv^zk_cmz.is`, with the precise
adversary transformation and query dependence part of that future
statement — are follow-up work, pending the upstream erratum; the
printed Theorem 5.3 blueprint node stays unanchored either way.

## The issuance protocol (Figure 9, boxes removed)

On public parameters `(X₀, Xᵣ, X⃗)` and attributes `m⃗`:

- **User, first move**: sample `s ←$ ℤ_p`; send the Pedersen commitment
  `C' = Σᵢ mᵢ·Xᵢ + s·G₀`, keeping `s` as state.
- **Server**: sample `u ←$ F×`; answer `U' = u·G₀`,
  `V' = x₀·U' + u·(C' + Xᵣ)` — unconditionally (`some` always; the
  abstract interface carries rejection only for μBBS_AT's sake).
- **User, second move**: check `U' ≠ 0`; sample `r ←$ F×`; unblind to
  the token `σ = (r·U', r·(V' − s·U'))`.

The unblinded token is `(U, macScalar·U)` for `U = (r·u)·G₀`: the
verification equation of the base MAC holds by construction, so
`verify` *is* the base MAC's `verify`.

## Punctured sampling and perfect correctness

The printed Figure 9 samples *both* issuance nonces from the full field
(`u ←$ ℤ_p` and `r ←$ ℤ_p`). We sample both from the punctured field
`F× = F ∖ {0}` (via `uniformUnits`, definitionally `uniformNonzero F`),
the same convention as the base MAC's tag base `U ←$ G×`
(`Construction.lean`, *Nonzero `U` and perfect correctness*):

- `u = 0` would make the honest run abort at the user's `U' ≠ 0` check;
- `r = 0` would make the honest run emit the invalid token `(0, 0)`
  (§5.1's rerandomization property itself demands `r ≠ 0`, so the
  figure's literal `r ←$ ℤ_p` appears to be an oversight).

Under the literal samplers an honest issuance thus fails with
probability `2/p − 1/p²` — mass that the repo's support-based
(probability-one) `ATSyntax.Correct` cannot absorb. Reductions
replaying the server or the user must account for these per-nonce `1/p`
distribution deltas, exactly as they do for the base MAC's tag base.

Correctness additionally needs the generator to be nonzero
(`hgen : gen ≠ 0`): the honest token base is `(r·u)·gen`, which the
verifier's `U ≠ 0` check rejects when `gen = 0`. The hypothesis is
carried explicitly by `μCMZATCore_correct` and the bundle — a plain
hypothesis, not the `Fact (Function.Bijective (· • gen))` instance of
the AGM layer, which is only needed once discrete logs are taken.

## Out of scope

- The one-more unforgeability analysis (O24 Theorem 5.11, Claims
  5.12–5.14) — the AGM-instrumented game and the polynomial layer land
  in `OneMoreUnforgeability.lean` (Track CMZ-OMUF).
- The anonymity clause of Theorem 5.3 — blocked on the Definition 4.4
  game and Theorem 5.8 (Track CMZ-A).
-/

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleComp

set_option autoImplicit false

/- The canonical game-construction variable block (`docs/STYLE_GUIDE.md`,
*Prime-order group convention*), as in `Construction.lean`. `F` is implicit for
the helpers (inferred from the scalar arguments) and reannotated to *explicit*
for the bundle-level defs, whose result types do not mention it. -/
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]

/--
Issuance, user's first move (O24 Figure 9): sample the blinding scalar
`s ←$ ℤ_p` and send the Pedersen commitment `C' = Σᵢ mᵢ·Xᵢ + s·G₀` over
the issuer's attribute bases `X⃗` (from `pp`) and the generator. The
issuance proof `π_iu` of Figure 9 is boxed (removed for anonymous
tokens); `s` is kept as the user's state for the unblinding move.
-/
noncomputable def atIssueUsr₁ {n : ℕ} (gen : G) (pp : Params G n) (m : Fin n → F) :
    ProbComp (F × G) := do
  let s ← $ᵗ F
  pure (s, (∑ i, m i • pp.2.2 i) + s • gen)

/--
Issuance, server's move (O24 Figure 9, π_is removed — see the module
docstring): sample `u ←$ F×` (punctured, where the paper writes
`u ←$ ℤ_p` — see *Punctured sampling* in the module docstring) and
answer `U' = u·G₀`, `V' = x₀·U' + u·(C' + Xᵣ)` with `Xᵣ = xᵣ·G₀`
recomputed from the secret key. Never rejects (`some` always): the
`Option` is the abstract interface's, carried for μBBS_AT's `C' ≠ 0`
check.
-/
noncomputable def atIssueSrv {n : ℕ} (gen : G) (sk : Key F n) (C' : G) :
    ProbComp (Option (G × G)) := do
  let u ← uniformUnits F
  let U' := u • gen
  pure (some (U', sk.1 • U' + u • (C' + sk.2.1 • gen)))

/--
Issuance, user's second move (O24 Figure 9): check `U' ≠ 0` (abort
otherwise), sample `r ←$ F×`, and unblind the server's response to
the token `σ = (r·U', r·(V' − s·U'))` using the blinding scalar `s` kept
from the first move. The re-randomizer is punctured where the figure
prints `r ←$ ℤ_p` — a repair, not just a convention: `r = 0` would emit
the invalid token `(0, 0)`, and §5.1's rerandomization property demands
`r ≠ 0` (see *Punctured sampling* in the module docstring).
-/
noncomputable def atIssueUsr₂ (s : F) (resp : G × G) : ProbComp (Option (Code G)) :=
  if resp.1 = 0 then pure none
  else do
    let r ← uniformUnits F
    pure (some (r • resp.1, r • (resp.2 - s • resp.1)))

-- Reannotate `F` as explicit for the bundle-level defs below: it does not
-- appear in their result types, so it must be supplied at each call site (the
-- `Construction.lean` convention). The helpers keep the implicit `{F}`.
variable (F)

/--
The μCMZ_AT **core** scheme as a syntactic anonymous token (O24 §5.6,
Figure 9 with *both* issuance proofs removed — see the module docstring
for why this deviates from the printed boxes, which remove only `π_iu`).

Setup, key generation, message space, and keyed verification are those
of the base MAC, shared definitionally: `toKeyedSetupSyntax` is
projected from `μCMZBaseMACSyntax` and `verify` *is* the base MAC's
`verify`, so every lemma about the base algorithms transfers verbatim.
The issuance carriers are

- `UsrState _ := F` — the blinding scalar `s`;
- `IssueMsg _ := G` — the Pedersen commitment `C'`;
- `BlindTok _ := G × G` — the server's blinded pair `(U', V')`;
- `Token _ := Code G` — the unblinded MAC tag `(U, V)`.

The generator `gen : G` (O24's `G₀ ∈ Γ`) is an explicit scheme
parameter, exactly as for `μCMZBaseMACSyntax`. Noncomputable for the
same reason (sampling via `Fintype.equivFin`).
-/
noncomputable def μCMZATCoreSyntax (gen : G) : ATSyntax ProbComp where
  toKeyedSetupSyntax := (μCMZBaseMACSyntax F gen).toKeyedSetupSyntax
  Token := fun _ => Code G
  UsrState := fun _ => F
  IssueMsg := fun _ => G
  BlindTok := fun _ => G × G
  issueUsr₁ := fun _ pp m => atIssueUsr₁ gen pp m
  issueSrv := fun _ sk μ => atIssueSrv gen sk μ
  issueUsr₂ := fun _ st resp => atIssueUsr₂ st resp
  verify := fun _ sk m t => verify sk m t

/--
Correctness of the μCMZ_AT core (the "correctness is straightforward"
clause of O24 Theorem 5.3, §5.6): every honestly issued token verifies,
in the support-based (probability-one) sense of `ATSyntax.Correct`.

The generator must be nonzero (`hgen`): the honest token base is
`(r·u)·G₀`, which verification rejects when `G₀ = 0`. With `u`, `r`
drawn from the punctured field, the base is then nonzero and the MAC
equation `V = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·U` holds by the unblinding algebra
`V' − s·U' = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·U'`.
-/
theorem μCMZATCore_correct (gen : G) (hgen : gen ≠ 0) :
    (μCMZATCoreSyntax F gen).Correct := by
  intro secParam n _hn crs _hcrs keys hkeys m σ? hσ?
  obtain ⟨⟨x₀, xᵣ, x⟩, pp⟩ := keys
  -- The keygen support pins `pp` to the secret key.
  have hpp := (mem_support_keygen (F := F) (G := G) crs gen x₀ xᵣ x pp).mp hkeys
  subst hpp
  -- Unfold the issuance chain: the user's `(s, C')`, the server's
  -- `some (U', V')` with `u ≠ 0`, and the unblinding.
  simp only [μCMZATCoreSyntax, ATSyntax.issue, atIssueUsr₁, atIssueSrv,
    bind_pure_comp, support_map, support_bind, support_uniformSample,
    mem_support_uniformUnits, Set.mem_image, Set.mem_univ, true_and] at hσ?
  obtain ⟨sC, ⟨s, hsC⟩, hσ?⟩ := Set.mem_iUnion₂.mp hσ?
  subst hsC
  obtain ⟨opt, ⟨u, hu, hopt⟩, hσ?⟩ := Set.mem_iUnion₂.mp hσ?
  subst hopt
  -- The server never sends `U' = 0`: `u ≠ 0` and `gen ≠ 0`.
  have hU' : u • gen ≠ 0 := smul_ne_zero hu hgen
  simp only [atIssueUsr₂, if_neg hU', support_bind, mem_support_uniformUnits,
    support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hσ?
  obtain ⟨r, hr, rfl⟩ := hσ?
  -- The unblinded pair is a valid MAC tag.
  refine ⟨_, rfl, ?_⟩
  simp only [μCMZATCoreSyntax, verify, macScalar, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · exact smul_ne_zero hr hU'
  · -- `r·(V' − s·U') = (x₀ + xᵣ + Σᵢ xᵢmᵢ)·(r·U')`: module algebra over `gen`.
    have hsum : ∀ v : Fin n → F,
        (∑ i, v i • (x i • gen)) = (∑ i, x i * v i) • gen := by
      intro v
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    rw [hsum m]
    simp only [smul_smul, ← add_smul, ← sub_smul]
    congr 1
    ring

/--
The μCMZ_AT core as a bundled `AnonymousToken` (O24 §3.4's
syntax-plus-correctness object): the syntactic scheme paired with its
correctness proof, over a nonzero generator `gen : G` (O24's `G₀ ∈ Γ` —
a generator of the prime-order group, hence nonzero; the hypothesis
makes that explicit).

Per the `AnonymousToken` layering, the bundle certifies *only* syntax
and correctness. One-more unforgeability stays the standalone game of
`KVAC.Preliminaries.AnonymousTokens.Security` (Track CMZ-OMUF states
Theorem 5.11 over it), and no unlinkability or anonymity claim is
carried — in particular, O24's anonymity argument for `μCMZ_AT`
verifies and extracts `π_is`, so it does not even apply to this
`π_is`-less core (the `π_is`-carrying variant is Phase B follow-up
work). Noncomputable (via `μCMZATCoreSyntax`).
-/
noncomputable def μCMZATCore (gen : G) (hgen : gen ≠ 0) : AnonymousToken :=
  ⟨μCMZATCoreSyntax F gen, μCMZATCore_correct F gen hgen⟩

end KVAC.Schemes.MicroCMZ
