/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Semar Augusto
-/
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Instances.OptionT
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# `simulateQ` plumbing: guarded oracles and never-fails-conditioned state projection

`guardImpl` wraps a stateful oracle implementation with a per-query assertion `good`: on a query
satisfying `good` it lifts the wrapped oracle's step into `OptionT ProbComp`, otherwise it
`failure`s. Running the guarded oracle therefore *aborts on the first bad query*, so
`Pr[⊥ | (simulateQ (guardImpl impl good) oa).run s] = 0` implies that no bad query is
reachable in any execution of `oa` against `impl`. The `OptionT` layer is where the failure
lives — plain `OracleComp` is a total free monad with no `failure` — and aborting *at* the bad
query gives the certificate the shape the projection proof consumes: `probFailure_bind_eq_zero_iff`
peels it one query at a time into "this query is good" and "every continuation never fails".

That never-fails hypothesis is exactly what conditions the projection theorem
`map_run_simulateQ_eq_of_guard_neverFails`: if every *good* oracle step of `impl₁` becomes the
corresponding `impl₂` step after projecting the state by `proj` (nothing is assumed about bad
steps), then the full simulated runs agree under the same projection. It is the
per-query-conditioned analogue of `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'`
(VCVio `…/SimSemantics/StateT/StateProjection.lean`), whose state invariant `inv : σ₁ → Prop`
cannot express goodness of the *query*: `good : spec.Domain → σ₁ → Prop` may reject a query from a
state that a different query is welcome to see. The conclusion is a term-level equality of
`ProbComp` computations, so any `probOutput`/`probEvent`/`evalDist` consequence follows by
`congrArg`.

Pure `OracleComp`/`StateT`/`OptionT` plumbing with no `F`/`G`/`MvPolynomial`, so it lives in this
VCVio-only leaf. It is specialised to `ProbComp`; generalising the base monad to `OracleComp spec'`,
as VCVio's `map_run_simulateQ_eq_of_query_map_eq_inv'` is, would make it upstreamable.
-/

set_option autoImplicit false

open OracleComp OracleSpec

namespace KVAC.Core

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- Guard a stateful oracle implementation with a per-query assertion: behave like `impl` (lifted
into `OptionT ProbComp`) on queries satisfying `good`, `failure` otherwise. Running under
`guardImpl impl good` aborts on the first bad query, so a `Pr[⊥ | …] = 0` hypothesis on the
guarded run certifies that no bad query is reachable. -/
def guardImpl (impl : QueryImpl spec (StateT σ₁ ProbComp))
    (good : (t : spec.Domain) → σ₁ → Prop) [∀ t s, Decidable (good t s)] :
    QueryImpl spec (StateT σ₁ (OptionT ProbComp)) :=
  fun t => StateT.mk fun s => if good t s then liftM ((impl t).run s) else failure

variable {impl : QueryImpl spec (StateT σ₁ ProbComp)}
    {good : (t : spec.Domain) → σ₁ → Prop} [∀ t s, Decidable (good t s)]

/-- On a good query the guarded oracle is the lifted wrapped oracle. -/
lemma guardImpl_run_pos {t : spec.Domain} {s : σ₁} (h : good t s) :
    (guardImpl impl good t).run s = liftM ((impl t).run s) :=
  if_pos h

/-- On a bad query the guarded oracle fails outright. -/
lemma probFailure_guardImpl_run_neg {t : spec.Domain} {s : σ₁} (h : ¬good t s) :
    Pr[⊥ | (guardImpl impl good t).run s] = 1 := by
  have hrun : (guardImpl impl good t).run s = (failure : OptionT ProbComp (spec.Range t × σ₁)) :=
    if_neg h
  simp [hrun, OptionT.probFailure_eq, OptionT.run_failure]

/-- Unfold one never-failing guarded step: the query was good, and the continuation never fails
from any result of the (unguarded) step. -/
private lemma good_and_neverFails_of_probFailure_guard_bind_eq_zero {t : spec.Domain} {s : σ₁}
    {β : Type} {cont : spec.Range t × σ₁ → OptionT ProbComp β}
    (h : Pr[⊥ | (guardImpl impl good t).run s >>= cont] = 0) :
    good t s ∧ ∀ x ∈ support (m := ProbComp) ((impl t).run s), Pr[⊥ | cont x] = 0 := by
  rw [probFailure_bind_eq_zero_iff] at h
  obtain ⟨hhead, hcont⟩ := h
  have hgood : good t s := by
    by_contra hbad
    rw [probFailure_guardImpl_run_neg hbad] at hhead
    exact one_ne_zero hhead
  exact ⟨hgood, fun x hx => hcont x (by rwa [guardImpl_run_pos hgood, OptionT.support_liftM])⟩

/-- Never-fails-conditioned state-projection transport for `simulateQ.run`.

If each *good* oracle call under `impl₁` becomes the corresponding `impl₂` call after mapping the
state with `proj`, and the `good`-guarded run of `oa` under `impl₁` never fails (so no bad query
is reachable), then the full simulated runs agree under the same projection. Per-query-conditioned
analogue of `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'`. -/
theorem map_run_simulateQ_eq_of_guard_neverFails
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (good : (t : spec.Domain) → σ₁ → Prop) [∀ t s, Decidable (good t s)] (proj : σ₁ → σ₂)
    (hproj : ∀ t s, good t s → Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁)
    (hnf : Pr[⊥ | (simulateQ (guardImpl impl₁ good) oa).run s] = 0) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind] at hnf ⊢
      obtain ⟨hgood, hcont⟩ := good_and_neverFails_of_probFailure_guard_bind_eq_zero hnf
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) :=
              bind_congr_of_forall_mem_support
                (mx := ((impl₁ t).run s : ProbComp (spec.Range t × σ₁)))
                (fun x hx => ih x.1 x.2 (hcont x hx))
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) :=
              (bind_map_left (Prod.map id proj) ((impl₁ t).run s)
                (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
              rw [hproj t s hgood]

end KVAC.Core
