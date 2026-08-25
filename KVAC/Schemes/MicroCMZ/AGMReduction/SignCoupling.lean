/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import KVAC.Schemes.MicroCMZ.AGMReduction.Coupling
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# μCMZ AGM unforgeability — the deterministic core, sign arm

The *deterministic* half of the reduction ↔ honest-game coupling, for the `sign`
oracle arm and the log invariants it establishes:

- `reductionSignStep_relTriple` — the reduction's `sign` step and the honest 
one are coupled and preserve
  `Coupling`'s `redLogHonestInv`;
- `redLog_honest` / `redLog_U_form` / `redLog_transcript_facts` — the log
  invariants that feed the eval bridge, packaged for the coupling proofs;
- `verifPoly_eval_embed_eq_zero` — the arity-clean brick that reads the
  vanishing fact off a `RedEmbedding` hypothesis rather than the raw equations.

`macScalar_maskedKey_expand` is the hinge between the two normal forms of the
masked key scalar. What this file states speaks the `macScalar (maskedKey …)`
form that `Coupling`'s `redLogHonestInv` uses, so a caller holding the state
invariant never has to convert; the eval bridge lemmas underneath — `Core`'s
`agmRepr_eval_eq_eval_toPoly` — want the key spelled out as `x₀ + xᵣ + m·x₁`
instead, and this is the lemma that trades one form for the other.

Everything here is deterministic algebra plus one distributional equality lifted
to a relational triple; no probability *bounds* — the counting layer sits above it.
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

/- The setting: a sampleable prime-order carrier, the generator `G₀` (O24's `G₀ ∈ Γ`; see
the note in `AGMReduction/Core.lean`) and its bijectivity, and the security parameter that
`agmOracleImpl` threads (the honest-game API; the reduction side doesn't take it). -/
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/-! ## Deterministic core (Piece A) -/

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- **The masked key scalar, expanded.** `Coupling`'s `macScalar_maskedKey_eq` in the *other* normal
form: `redLogHonestInv`, and everything stated in this file, speak
`macScalar (maskedKey x aM bM)`, while the eval bridge lemmas — `Core`'s
`agmRepr_eval_eq_eval_toPoly` and its companions — take their `htag` with the key spelled out as
`x₀ + xᵣ + m·x₁` at the masked secrets `xₖ = aₖ + x·bₖ`. This is the one lemma that trades one
spelling for the other. It also witnesses that the scalar depends on `m` only through `m 0`,
which is what lets the `Fin 1` transcript index and an `F`-valued message list line up. -/
lemma macScalar_maskedKey_expand (aM bM : FixedMasks F) (x : F) (m : Fin 1 → F) :
    macScalar (maskedKey x aM bM) m
      = (aM.x0 + x * bM.x0) + (aM.xr + x * bM.xr) + m 0 * (aM.x1 + x * bM.x1) := by
  simp only [macScalar, Fin.sum_univ_one, mul_comm]

section B2SignCoupling
open OracleComp.ProgramLogic.Relational

/-- **Sign-step coupling** (the novel core; the fidelity sentence of O24 Eq. 14). The
reduction's `sign` step (`reductionSignStep`) and the honest `sign` step
(`agmOracleImpl (.sign _)` at `Coupling`'s `maskedKey x aM bM`, the honest key read at the
masked secrets `(a₀+x·b₀, aᵣ+x·bᵣ, a₁+x·b₁)`) produce identically-distributed tags and preserve
`redLogHonestInv`: `sign_masked_tag_dist_eq` and `Core`'s `embedTag_eq` make the computed tag
`(U, V = key·U)`'s distribution match `mac (maskedKey x aM bM) m`;
`relTriple_map_eq` lifts this to the "computed tag = sampled tag" relation,
`relTriple_post_mono` adds the `redLogHonestInv`-preservation conjunct, and `relTriple_map`
threads both through the state append (the new red log entry `(m,(U,V),au,bu)` projects to the
new honest log entry `(m,(U,V))`, and `V = key·U` extends honesty). -/
lemma reductionSignStep_relTriple (x : F) (aM bM : FixedMasks F) (ep : EmbeddedParams G)
    (m : Fin 1 → F) (L : RedLog F G) (log : AGMLog F G 1)
    (hR : redLogHonestInv gen x aM bM L log) :
    RelTriple
      ((reductionSignStep gen (x • gen) (x ^ 2 • gen)
        aM bM m).run L)
      ((agmOracleImpl gen secParam (maskedKey x aM bM) ep.h
          (ep.x0, ep.xr, fun _ => ep.x1)
          (.sign m)).run log)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ redLogHonestInv gen x aM bM p₁.2 p₂.2) := by
  let X : G := x • gen
  let Mask := {p : F × F // p.1 • gen + p.2 • X ≠ 0}
  let Uf (aubu : Mask) : G := aubu.val.1 • gen + aubu.val.2 • X
  -- `Vf` is spelled in `keyCoeff` form, which is literally how `reductionSignStep` builds `V`.
  let Vf (aubu : Mask) : G :=
    (aM.keyCoeff (m 0) * aubu.val.1) • gen
      + (aM.keyCoeff (m 0) * aubu.val.2 + bM.keyCoeff (m 0) * aubu.val.1) • X
      + (bM.keyCoeff (m 0) * aubu.val.2) • (x ^ 2 • gen)
  let key : F := aM.keyCoeff (m 0) + x * bM.keyCoeff (m 0)
  have hV : ∀ aubu : Mask, Vf aubu = key • Uf aubu := fun aubu =>
    embedTag_eq gen aM bM x (m 0) aubu.val.1 aubu.val.2
  have hKey : macScalar (maskedKey x aM bM) m = key := macScalar_maskedKey_eq aM bM x m
  have hTag : evalDist ((fun aubu : Mask => (Uf aubu, Vf aubu)) <$>
      reductionMaskSample (gen := gen) X) =
      evalDist (mac (maskedKey x aM bM) m) := by
    have h2 := sign_masked_tag_dist_eq (G := G) gen x key
    -- State the bridge in `uniformNonzero` form — the shape `sign_masked_tag_dist_eq` uses.
    -- Spelling it as the raw subtype sample (`$ᵗ {g // g ≠ 0}` + `.val`) used to unify with `h2`
    -- by cross-associativity defeq; that silent unification is gone, so keep `uniformNonzero`
    -- folded and only unfold `mac`.
    have h3 : mac (maskedKey x aM bM) m =
        (do let U ← uniformNonzero G
            pure ((U, key • U) : G × G)) := by
      unfold mac
      rw [hKey]
    have hLHS : (fun aubu : Mask => (Uf aubu, Vf aubu))
        = (fun aubu : Mask => (Uf aubu, key • Uf aubu)) := by
      funext aubu; exact congrArg (Prod.mk (Uf aubu)) (hV aubu)
    rw [hLHS]
    exact h2.trans (congrArg evalDist h3).symm
  have hFirst : RelTriple (reductionMaskSample (gen := gen) X) (mac (maskedKey x aM bM) m)
      (fun aubu σ => (Uf aubu, Vf aubu) = σ) :=
    relTriple_map_eq (reductionMaskSample (gen := gen) X) (fun aubu : Mask => (Uf aubu, Vf aubu))
      (mac (maskedKey x aM bM) m) hTag
  have hFirst' : RelTriple (reductionMaskSample (gen := gen) X) (mac (maskedKey x aM bM) m)
      (fun aubu σ =>
        (Uf aubu, Vf aubu) = σ ∧
          redLogHonestInv gen x aM bM
            (L ++ [⟨m, (Uf aubu, Vf aubu), aubu.val.1, aubu.val.2⟩]) (log ++ [(m, σ)])) := by
    refine relTriple_post_mono hFirst ?_
    intro aubu σ hUV
    refine ⟨hUV, ?_, ?_⟩
    · -- log correspondence: `(log ++ [(m,σ)]) = (L ++ [red-entry]).map (·.1, ·.2.1)`
      rw [List.map_append, ← hR.1]; congr 1; simp only [Uf, Vf, hUV, List.map_singleton]
    · -- both per-entry facts extend to the new red entry: `Uf = au·g + bu·X` (rfl) and
      -- `Vf = macScalar (maskedKey …) m • Uf` (`hKey` puts `hV`'s `key` in `macScalar` form)
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hR.2 e he
      · obtain rfl : e = ⟨m, (Uf aubu, Vf aubu), aubu.val.1, aubu.val.2⟩ :=
          List.mem_singleton.mp he
        exact ⟨rfl, by rw [hKey]; exact hV aubu⟩
  simp only [reductionSignStep, agmOracleImpl, StateT.run_mk]
  exact relTriple_map hFirst'

end B2SignCoupling

/-! ## log invariants -/

/-- **(log-honesty invariant), shared core.** `redLog_honest` and `redLog_U_form` are two
projections of the same `simulateQ`-preserved invariant, so their identical case split is proved
once here. -/
private lemma redLog_honest_and_U_form (x : F) (aM bM : FixedMasks F) (ep : EmbeddedParams G)
    {β : Type} (oa : OracleComp (AGMOracleSpec F G 1) β) (out : β × RedLog F G)
    (hout : out ∈ support ((simulateQ
      (reductionOracleImpl gen (x • gen) (x ^ 2 • gen) (x ^ 3 • gen)
        aM bM ep) oa).run [])) :
    (∀ e ∈ out.2, e.tag.2 = macScalar (maskedKey x aM bM) e.msg • e.tag.1)
      ∧ ∀ e ∈ out.2, e.tag.1 = e.au • gen + e.bu • (x • gen) := by
  have hInv : QueryImpl.PreservesInv
      (reductionOracleImpl gen (x • gen) (x ^ 2 • gen) (x ^ 3 • gen) aM bM ep)
      (fun L : RedLog F G =>
        (∀ e ∈ L, e.tag.2 = macScalar (maskedKey x aM bM) e.msg • e.tag.1)
        ∧ ∀ e ∈ L, e.tag.1 = e.au • gen + e.bu • (x • gen)) := by
    intro t σ0 hσ0 z hz
    cases t with
    | sign m =>
        simp only [reductionOracleImpl, reductionSignStep] at hz
        -- `rw`/`simp` keyed on `?mx >>= ?my` no longer matches do-desugared binds (Lean 4.29+
        -- picks a syntactically different `Bind`), so apply the iff as a term: `_` placeholders
        -- unify up to defeq and see through `StateT.mk`/`StateT.run` as well.
        replace hz := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨aubu, -, hz⟩ := hz
        subst hz
        refine ⟨fun e he => ?_, fun e he => ?_⟩ <;>
          simp only [List.mem_append, List.mem_singleton] at he
        · rcases he with he | rfl
          · exact hσ0.1 e he
          · rw [macScalar_maskedKey_eq]
            exact embedTag_eq gen aM bM x (m 0) aubu.val.1 aubu.val.2
        · rcases he with he | rfl
          · exact hσ0.2 e he
          · rfl
    | verify m σ ρU ρV =>
        simp only [reductionOracleImpl, reductionVerifyStep] at hz
        subst hz; exact hσ0
    | help A₀ Av Z ρ₀ ρA ρZ =>
        simp only [reductionOracleImpl, reductionHelpStep] at hz
        subst hz; exact hσ0
  exact simulateQ_run_preservesInv _ _ hInv oa [] ⟨fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩ out hout

/-- **(log-honesty invariant).** With the genuine powers `X = x·g`, `X' = x²·g`, `X'' = x³·g`,
every tag the reduction's simulated oracle logs is honest — `Vⱼ = macScalar (maskedKey …) mⱼ · Uⱼ`,
the same `macScalar` form `redLogHonestInv` states the relation in, so a caller can move between
the two without a conversion. The `sign` branch appends only honest tags (`embedTag_eq`, retyped
by `macScalar_maskedKey_eq`); `verify`/`help` leave the log unchanged. Proved by
`simulateQ_run_preservesInv`; feeds `redLog_transcript_facts`. -/
lemma redLog_honest (x : F) (aM bM : FixedMasks F) (ep : EmbeddedParams G)
    {β : Type} (oa : OracleComp (AGMOracleSpec F G 1) β) (out : β × RedLog F G)
    (hout : out ∈ support ((simulateQ
      (reductionOracleImpl gen (x • gen) (x ^ 2 • gen) (x ^ 3 • gen)
        aM bM ep) oa).run [])) :
    ∀ e ∈ out.2, e.tag.2 = macScalar (maskedKey x aM bM) e.msg • e.tag.1 :=
  (redLog_honest_and_U_form gen x aM bM ep oa out hout).1

/-- Companion to `redLog_honest`: every logged tag's `Uⱼ` is `auⱼ·g + buⱼ·X` (`X = x·g`) — the
oracle builds it that way and records `(auⱼ, buⱼ)`, so the `sign` case is `rfl`. Supplies the tag
form `gamePoint_eq_embed_affine` needs. -/
lemma redLog_U_form (x : F) (aM bM : FixedMasks F) (ep : EmbeddedParams G)
    {β : Type} (oa : OracleComp (AGMOracleSpec F G 1) β) (out : β × RedLog F G)
    (hout : out ∈ support ((simulateQ
      (reductionOracleImpl gen (x • gen) (x ^ 2 • gen) (x ^ 3 • gen)
        aM bM ep) oa).run [])) :
    ∀ e ∈ out.2, e.tag.1 = e.au • gen + e.bu • (x • gen) :=
  (redLog_honest_and_U_form gen x aM bM ep oa out hout).2

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G]
  [SampleableGroup F G] in
/-- **Index bridge.** With `tags` the log's tag list, the `Fin.cast`-indexed `j`-th game tag is
the `j`-th log entry's tag `(Uⱼ, Vⱼ)`. This is what transports per-log-entry invariants onto
`tags`-indexed statements. -/
private lemma redLog_tags_get_cast {L : RedLog F G} {tags : List (G × G)}
    (htags : tags = L.map (fun e : SignRecord F G => e.tag))
    (hlen : tags.length = L.length) (j : Fin L.length) :
    tags.get (Fin.cast hlen.symm j) = (L.get j).tag := by
  subst htags
  simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]

omit hgen in
/-- **Transcript facts, index-transported.** Log-honesty (`Vⱼ = keyⱼ·Uⱼ` at the real logs
`xₖ = aₖ + x·bₖ`) and the embedded `U`-form (`Uⱼ = auⱼ·g + buⱼ·X`), carried from their
per-log-entry forms onto the transcript along `redLog_tags_get_cast` — the content from which
the eval bridge lemmas' `htag`/`U`-form hypotheses are assembled. The conclusion
stays indexed by `Fin L.length` (reaching `tags` entries through the cast) and keeps the
`macScalar (maskedKey …)` key spelling; a caller still trades the index type and the key
spelling at the use site.

Its inputs are the two components of `redLogHonestInv`'s per-entry conjunction — split as
`fun e he => (hR.2 e he).2` and `fun e he => (hR.2 e he).1` — which are also exactly the
conclusions of `redLog_honest` / `redLog_U_form`, so one lemma serves both a caller holding the
state invariant and a caller holding only support membership of a `simulateQ` run. Both sides
speak `macScalar (maskedKey …)`, so nothing is converted here; `macScalar_maskedKey_expand` appears
only to see that at arity 1 the key reads its message at `0` alone, which is what lets an entry's
own `msg` match the `fun _ => msgs j` the transcript-indexed consumers take.

Returned as a conjunction rather than a structure, matching `redLog_honest_and_U_form`'s shape
and avoiding a single-use type. -/
lemma redLog_transcript_facts {x : F} {aM bM : FixedMasks F} {L : RedLog F G}
    (hhon : ∀ e ∈ L, e.tag.2 = macScalar (maskedKey x aM bM) e.msg • e.tag.1)
    (hUform : ∀ e ∈ L, e.tag.1 = e.au • gen + e.bu • (x • gen))
    {tags : List (G × G)} (htags : tags = L.map (fun e : SignRecord F G => e.tag))
    (hlen : tags.length = L.length) :
    (∀ j : Fin L.length, (tags.get (Fin.cast hlen.symm j)).2
        = macScalar (maskedKey x aM bM) (fun _ => (L.get j).msg 0)
          • (tags.get (Fin.cast hlen.symm j)).1)
      ∧ ∀ j : Fin L.length, (tags.get (Fin.cast hlen.symm j)).1
        = (L.get j).au • gen + (L.get j).bu • (x • gen) :=
  ⟨fun j => by
      rw [redLog_tags_get_cast htags hlen j]
      -- `macScalar` at arity 1 reads its message only at `0`, so the entry's own `msg` and the
      -- `fun _ => msg 0` the transcript-indexed consumers take agree; `_expand` sees that.
      simpa only [macScalar_maskedKey_expand] using hhon (L.get j) (List.get_mem L j),
   fun j => by
      rw [redLog_tags_get_cast htags hlen j]; exact hUform (L.get j) (List.get_mem L j)⟩

/-- Packages `verifPoly_eval_eq_zero_of_keySmul` + `gamePoint_eq_embed_affine` at 
an *abstract* arity `q` tied to the transcript by `hq : tags.length = q`. 
Stating the arity as a variable lets us `subst hq` 
(which collapses the `Fin.cast`s the transcript log forces), so the caller can
instantiate `q := L.length` and read off the verification polynomial vanishing at the
embedded point `v ↦ a v + x·b v` with no dependent-cast bookkeeping. -/
lemma verifPoly_eval_embed_eq_zero {q : ℕ} (ρU ρV : AGMRepr F 1)
    (x : F) (aM bM : FixedMasks F) (ep : EmbeddedParams G)
    (hemb : RedEmbedding gen x aM bM ep)
    (ca cb msgs : Fin q → F) (mStar0 : F)
    (tags : List (G × G)) (hq : tags.length = q)
    (htf : (∀ j : Fin q, (tags.get (Fin.cast hq.symm j)).2
        = macScalar (maskedKey x aM bM) (fun _ => msgs j)
          • (tags.get (Fin.cast hq.symm j)).1)
      ∧ ∀ j : Fin q, (tags.get (Fin.cast hq.symm j)).1
        = ca j • gen + cb j • (x • gen))
    (hkey : ρV.evalAt gen ep tags
      = macScalar (maskedKey x aM bM) (fun _ => mStar0) • ρU.evalAt gen ep tags) :
    MvPolynomial.eval
        (fun v => FixedMasks.embed aM ca v
          + x * FixedMasks.embed bM cb v)
        (AGMPoly.verifPoly msgs mStar0 (ρU.toReprCoeffs q) (ρV.toReprCoeffs q)) = 0 := by
  rw [AGMRepr.evalAt_of_redEmbedding gen hemb, AGMRepr.evalAt_of_redEmbedding gen hemb]
    at hkey
  subst hq
  -- Trade the `macScalar` key for the spelled-out one the abstract-arity lemma takes.
  simp only [macScalar_maskedKey_expand] at htf hkey
  have key := verifPoly_eval_eq_zero_of_keySmul gen ρU ρV
    (aM.eta • gen + bM.eta • (x • gen)) (aM.x0 + x * bM.x0) (aM.xr + x * bM.xr)
    (fun _ => aM.x1 + x * bM.x1) mStar0 tags msgs htf.1 hkey
  rwa [gamePoint_eq_embed_affine gen x aM bM
    (aM.eta • gen + bM.eta • (x • gen)) tags ca cb rfl htf.2] at key

end KVAC.Schemes.MicroCMZ
