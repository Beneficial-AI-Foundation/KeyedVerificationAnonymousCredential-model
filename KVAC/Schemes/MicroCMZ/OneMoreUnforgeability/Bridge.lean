/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jin Xing Lim
-/
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Game
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.CaseEvents

/-!
# μCMZ_AT one-more unforgeability — the pigeonhole step and the evaluation bridge (O24 §5.6)

The facts about a winning run of the `n = 1` game that the case analysis of the Theorem 5.11
proof (p. 45) rests on, none of which is a statement about a reduction. Track CMZ-OMUF, step A3 of
the Theorem 5.3 plan, part 17a of item 17.

- the pigeonhole step: a winning run has a forgery whose polynomial (Equation 22) is nonzero
  (`OMUFTrace.exists_forgeryPoly_ne_zero`);
- the evaluation bridge: for a run in the support of `agmOMUFTrace`, the public parameters are the
  key's and every issued pair answers its commitment as the server does
  (`OMUFTrace.serverConsistent_of_mem_support`), and so at the discrete-log point of the run
  `t.cs k` evaluates to the logarithm of the `k`-th issued commitment and the polynomial of a
  verifying forgery vanishes (`OMUFTrace.eval_point_cs`, `OMUFTrace.eval_point_forgeryPoly`);
- the case cover: a win gives one of the three case events (`omuf_cover`).
-/

set_option autoImplicit false

namespace KVAC.Schemes.MicroCMZ

open KVAC.Core KVAC.Preliminaries OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]


variable (gen : G)
variable [hgen : Fact (Function.Bijective (fun x : F => x • gen))]
variable (secParam : ℕ)

/-- A duplicate-free list all of whose entries are values of a function out of `Fin n` has at most
`n` entries (pigeonhole). -/
theorem length_le_of_nodup_of_forall_mem_range {α : Type*} [DecidableEq α] {n : ℕ} {l : List α}
    (hnd : l.Nodup) (f : Fin n → α) (h : ∀ x ∈ l, ∃ j, x = f j) : l.length ≤ n := by
  have hsub : l.toFinset ⊆ Finset.univ.image f := by
    intro x hx
    obtain ⟨j, hj⟩ := h x (List.mem_toFinset.1 hx)
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, hj.symm⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  exact this.trans (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]))

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] [SampleableGroup F G] in
/-- The `u`-free part of the `k`-th commitment polynomial of a run is that of the `k`-th issued
representation (Equation 18, via `ev0_omufCommitPolys_getElem`). -/
theorem OMUFTrace.ev0_cs (t : OMUFTrace F G) (k : Fin t.arity) :
    AGMPoly.ev0 (t.cs k) = (t.issuedCoeffs k).uFree := by
  rw [OMUFTrace.cs_eq_getElem]
  unfold OMUFTrace.commitPolys
  rw [AGMPoly.ev0_omufCommitPolys_getElem]
  simp [OMUFTrace.issuedCoeffs, OMUFTrace.issuedRepr]

omit hgen in
/-- A forgery with a vanishing polynomial and a nonzero `U` has its message at the `x₁`
coefficient of some issued representation: the coefficient reading of Equations 20 and 21
(`forgeryPoly_eq_zero_coeffs`) leaves `U` a combination of the issued `U'_j` alone, so a
nonzero `U` has a nonzero `cu j`, and that slot fixes `m`. -/
theorem OMUFTrace.msg_mem_of_forgeryPoly_eq_zero (t : OMUFTrace F G)
    (e : AGMOMUFForgery F G 1) (hU : e.token.1 ≠ 0)
    (hm : reprMatches e.reprU gen t.H t.pp.1 t.pp.2.1 t.pp.2.2 (AGMOMUFLog.tags t.log)
      e.token.1)
    (hφ : AGMPoly.omufForgeryPoly t.cs (e.msg 0) (e.reprU.toReprCoeffs t.arity)
      (e.reprV.toReprCoeffs t.arity) = 0) :
    ∃ j : Fin t.arity, e.msg 0 = (t.issuedCoeffs j).c1 := by
  obtain ⟨hg, hh, h0, hr, h1, hv, hu⟩ :=
    AGMPoly.forgeryPoly_eq_zero_coeffs t.cs t.issuedCoeffs t.ev0_cs (e.msg 0) _ _ hφ
  by_contra hno
  push Not at hno
  have hcu : ∀ j : Fin t.arity, (e.reprU.toReprCoeffs t.arity).cu j = 0 := by
    intro j
    rcases mul_eq_zero.1 (hu j) with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) (hno j)
  apply hU
  rw [← hm.2]
  unfold AGMRepr.eval
  have hsum : (List.zipWith (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2)
      e.reprU.uv (AGMOMUFLog.tags t.log)).sum = 0 := by
    rw [sum_zipWith_eq_fin_sum_getD
      (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2) (0, 0) (0, 0) (by simp)]
    apply Finset.sum_eq_zero
    intro j _
    have h1 := hcu j
    have h2 := hv j
    simp only [AGMRepr.toReprCoeffs] at h1 h2
    change (e.reprU.uv.getD (j : ℕ) (0, 0)).1 • ((AGMOMUFLog.tags t.log).get j).1 +
      (e.reprU.uv.getD (j : ℕ) (0, 0)).2 • ((AGMOMUFLog.tags t.log).get j).2 = 0
    rw [h1, h2]
    simp
  simp only [AGMRepr.toReprCoeffs] at hg hh h0 hr h1
  simp [hg, hh, h0, hr, h1, hsum]

omit hgen in
/-- A winning run has a forgery whose polynomial is nonzero: were all `φ_i = 0`, the `q + 1`
forged messages would lie in the at most `r ≤ q` values `x₁`-coefficient of the issued
representations (`msg_mem_of_forgeryPoly_eq_zero`), against their distinctness. The pigeonhole
step of O24 p. 45. -/
theorem OMUFTrace.exists_forgeryPoly_ne_zero (t : OMUFTrace F G)
    (hw : t.Wins gen secParam) : ∃ φ ∈ t.forgeryPolys, φ ≠ 0 := by
  by_contra h
  simp only [ne_eq, not_exists, not_and, Decidable.not_not] at h
  obtain ⟨⟨hlen, hnodup, hver⟩, hrepr⟩ := hw
  simp only [List.length_map] at hlen
  let f : Fin t.arity → F := fun j => (t.issuedCoeffs j).c1
  have hmem : ∀ e ∈ t.out, ∃ j, e.msg 0 = f j := by
    intro e he
    have hU : e.token.1 ≠ 0 := by
      have := hver (e.plain) (List.mem_map_of_mem he)
      simp only [μCMZATCoreSyntax, verify, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    exact t.msg_mem_of_forgeryPoly_eq_zero gen e hU (hrepr e he).1
      (h _ (List.mem_map_of_mem he))
  have hinj : Function.Injective fun m : Fin 1 → F => m 0 := by
    intro a b hab
    funext i
    rw [Subsingleton.elim i 0]
    exact hab
  have hnd : (t.out.map fun e => e.msg 0).Nodup := by
    have e1 : t.out.map (fun e => e.msg 0) = List.map (fun m : Fin 1 → F => m 0)
        (List.map Prod.fst (List.map AGMOMUFForgery.plain t.out)) := by
      simp [List.map_map, Function.comp_def, AGMOMUFForgery.plain]
    rw [e1]
    exact hnodup.map hinj
  have h1 : (t.out.map fun e => e.msg 0).length ≤ t.arity :=
    length_le_of_nodup_of_forall_mem_range hnd f (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact hmem e he)
  rw [List.length_map] at h1
  have h3 : t.arity ≤ t.log.length := AGMOMUFLog.tags_length_le t.log
  have hlen' : t.out.length = t.log.length + 1 := hlen
  omega

/-! ### The evaluation bridge of a run

A run fixes a point of the polynomial ring of the run: the logarithms of the crs and of
the key, and, for each issued pair, the logarithm of its first component, which the server
sampled and the trace does not store but `U'_j = u_j • gen` determines. -/

omit hgen in
/-- What the support of `agmOMUFTrace` guarantees about a run: the public parameters are the
key's, and the `k`-th issued pair answers a commitment `C'` whose representation `issuedRepr k`
passed the gate at the pairs before it, with the server's answer `U' = u • gen`,
`V' = x₀ • U' + u • (C' + xᵣ • gen)` (`atIssueSrv`). -/
def OMUFTrace.ServerConsistent (t : OMUFTrace F G) : Prop :=
  t.pp = (t.sk.1 • t.H, t.sk.2.1 • gen, fun i => t.sk.2.2 i • gen) ∧
    ∀ k : Fin t.arity, ∃ C' : G,
      reprMatches (t.issuedRepr k) gen t.H t.pp.1 t.pp.2.1 t.pp.2.2
        ((AGMOMUFLog.tags t.log).take k) C' ∧
      ∃ u : F, ((AGMOMUFLog.tags t.log).get k).1 = u • gen ∧
        ((AGMOMUFLog.tags t.log).get k).2 =
          t.sk.1 • ((AGMOMUFLog.tags t.log).get k).1 + u • (C' + t.sk.2.1 • gen)

/-- The point of the run: `η = log H`, the key, and `u_j = log` of the `j`-th issued `U'`
(`gamePoint`, at the run's pairs). -/
noncomputable def OMUFTrace.point (t : OMUFTrace F G) : AGMPoly.Var t.arity → F :=
  gamePoint gen t.H t.sk.1 t.sk.2.1 (t.sk.2.2 0) (AGMOMUFLog.tags t.log)

/-! #### Issuance positions in a log

The `k`-th issued pair sits at some log position `i`, with exactly `k` issued pairs before it.
These lemmas are about `filterMap` alone. -/

/-- The `k`-th kept element of a `filterMap` comes from some position `i` of the list, with
exactly `k` kept elements before it. -/
theorem exists_index_of_getElem_filterMap {α β : Type*} (f : α → Option β) (l : List α)
    (k : ℕ) (hk : k < (l.filterMap f).length) :
    ∃ (i : ℕ) (x : α), l[i]? = some x ∧ f x = some (l.filterMap f)[k] ∧
      ((l.take i).filterMap f).length = k := by
  induction l using List.reverseRecOn generalizing k with
  | nil => simp only [List.filterMap_nil, List.length_nil, _root_.not_lt_zero] at hk
  | append_singleton xs x tail_ih =>
    simp only [List.filterMap_append]
    rw [List.filterMap_append] at hk
    cases h : f x with
    | none =>
      simp_all only [List.filterMap_cons_none, List.filterMap_nil, List.append_nil]
      obtain ⟨i, y, hix_l, hix_r⟩ := tail_ih k hk
      have hi := (List.getElem?_eq_some_iff.1 hix_l).1
      refine ⟨i, y, ?_, ?_⟩
      · rw [List.getElem?_append_left hi, hix_l]
      · rw [List.take_append_of_le_length hi.le]
        exact hix_r
    | some v =>
      simp_all only [Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil,
        List.length_append, List.length_cons, List.length_nil, zero_add, Order.lt_add_one_iff]
      cases Nat.eq_or_lt_of_le hk with
      | inl k_eq =>
        subst k_eq
        refine ⟨xs.length, x, ?_, ?_⟩
        · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          exact List.getElem?_cons_zero
        · rw [List.getElem_append_right (Nat.le_refl _)]
          refine ⟨?_, ?_⟩
          · simp only [Nat.sub_self, List.getElem_cons_zero]
            exact h
          · simp only [List.take_left']
      | inr k_le =>
        obtain ⟨i, y, hix_l, hix_r⟩ := tail_ih k k_le
        have hi := (List.getElem?_eq_some_iff.1 hix_l).1
        refine ⟨i, y, ?_, ?_⟩
        · rw [List.getElem?_append_left hi, hix_l]
        · rw [List.getElem_append_left, List.take_append_of_le_length hi.le]
          exact hix_r

/-- The kept elements of a prefix are a prefix of the kept elements: the first
`((l.take i).filterMap f).length` of them. -/
theorem filterMap_take_eq_take {α β : Type*} (f : α → Option β) (l : List α) (i : ℕ) :
    (l.take i).filterMap f = (l.filterMap f).take ((l.take i).filterMap f).length := by
  have h : l.filterMap f = (l.take i).filterMap f ++ (l.drop i).filterMap f := by
    rw [← List.filterMap_append, List.take_append_drop]
  rw [h, List.take_left]

/-- The issued entries of a log, each representation with its issued pair, in issuance order. -/
def AGMOMUFLog.issued {n : ℕ} (log : AGMOMUFLog F G n) : List (AGMRepr F n × (G × G)) :=
  log.filterMap fun e => e.2.2.map fun p => (e.2.1, p)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G]
  [SampleableGroup F G] in
/-- The issued pairs are the second components of the issued entries. -/
theorem AGMOMUFLog.tags_eq_map_issued {n : ℕ} (log : AGMOMUFLog F G n) :
    AGMOMUFLog.tags log = log.issued.map Prod.snd := by
  unfold AGMOMUFLog.tags AGMOMUFLog.issued
  rw [List.map_filterMap]
  congr 1
  funext e
  cases e.2.2 <;> simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G]
  [SampleableGroup F G] in
/-- The issued representations are the first components of the issued entries. -/
theorem OMUFTrace.issuedReprs_eq_map_issued (t : OMUFTrace F G) :
    t.issuedReprs = t.log.issued.map Prod.fst := by
  unfold OMUFTrace.issuedReprs AGMOMUFLog.issued
  rw [List.map_filterMap]
  congr 1
  funext e
  cases e.2.2 <;> simp

omit hgen in
/-- The server's answers: `atIssueSrv` returns `(u • gen, x₀ • (u • gen) + u • (C' + xᵣ • gen))`
for a nonzero scalar `u`. -/
theorem mem_support_atIssueSrv {n : ℕ} (sk : Key F n) (C' : G) (resp : Option (G × G)) :
    resp ∈ support (atIssueSrv gen sk C') ↔
      ∃ u : F, u ≠ 0 ∧ resp = some (u • gen, sk.1 • (u • gen) + u • (C' + sk.2.1 • gen)) := by
  simp only [atIssueSrv, smul_add, bind_pure_comp, support_map, Set.mem_image,
    mem_support_uniformUnits, ne_eq]
  constructor <;> rintro ⟨u, hu, h⟩ <;> exact ⟨u, hu, h.symm⟩

/-! #### The log invariant

What every issued entry of a reachable log satisfies, stated at the entry's own log position so
that appending an entry leaves the earlier ones alone. -/

omit hgen in
/-- Every issued entry of `log` passed the gate at the pairs issued before it and carries the
server's answer: `U' = u • gen` and `V' = x₀ • U' + u • (C' + xᵣ • gen)` (`atIssueSrv`). -/
def AGMOMUFLog.Consistent {n : ℕ} (sk : Key F n) (H : G) (pp : Params G n)
    (log : AGMOMUFLog F G n) : Prop :=
  ∀ (i : ℕ) (C' : G) (ρ : AGMRepr F n) (U' V' : G),
    log[i]? = some (C', ρ, some (U', V')) →
      reprMatches ρ gen H pp.1 pp.2.1 pp.2.2 (AGMOMUFLog.tags (log.take i)) C' ∧
        ∃ u : F, U' = u • gen ∧ V' = sk.1 • U' + u • (C' + sk.2.1 • gen)

omit hgen in
/-- The empty log is consistent. -/
theorem AGMOMUFLog.consistent_nil {n : ℕ} (sk : Key F n) (H : G) (pp : Params G n) :
    AGMOMUFLog.Consistent gen sk H pp ([] : AGMOMUFLog F G n) := by
  intro i C' ρ U' V' h
  simp at h

omit hgen in
/-- Appending an entry keeps a log consistent, provided the entry is consistent at the pairs
issued so far if it was issued. -/
theorem AGMOMUFLog.consistent_append {n : ℕ} {sk : Key F n} {H : G} {pp : Params G n}
    {log : AGMOMUFLog F G n} (hlog : AGMOMUFLog.Consistent gen sk H pp log)
    (e : G × AGMRepr F n × Option (G × G))
    (he : ∀ U' V', e.2.2 = some (U', V') →
      reprMatches e.2.1 gen H pp.1 pp.2.1 pp.2.2 (AGMOMUFLog.tags log) e.1 ∧
        ∃ u : F, U' = u • gen ∧ V' = sk.1 • U' + u • (e.1 + sk.2.1 • gen)) :
    AGMOMUFLog.Consistent gen sk H pp (log ++ [e]) := by
  intro i C' ρ U' V' h
  rcases lt_trichotomy i log.length with hi | rfl | hi
  · rw [List.getElem?_append_left hi] at h
    obtain ⟨hm, hu⟩ := hlog i C' ρ U' V' h
    refine ⟨?_, hu⟩
    rwa [List.take_append_of_le_length hi.le]
  · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.take_left]
    exact he U' V' rfl
  · rw [List.getElem?_eq_none (by simp; omega)] at h
    cases h

omit hgen in
/-- One query of the instrumented oracle keeps the log consistent: coin queries and `verify`
leave it alone, a refused `sign` appends an unissued entry, and an accepted one appends the
answer of `atIssueSrv`. -/
theorem agmOMUFImpl_preservesInv {n : ℕ} (secParam : ℕ) (sk : Key F n) (H : G)
    (pp : Params G n) :
    QueryImpl.PreservesInv (agmOMUFImpl gen secParam sk H pp)
      (AGMOMUFLog.Consistent gen sk H pp) := by
  intro q log hlog z hz
  rcases q with q | q
  · simp only [agmOMUFImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply] at hz
    change z ∈ support ((StateT.lift _).run log) at hz
    rw [StateT.run_lift, mem_support_bind_iff] at hz
    obtain ⟨a, -, ha⟩ := hz
    rw [mem_support_pure_iff] at ha
    subst ha
    exact hlog
  · rw [agmOMUFImpl_inr] at hz
    rcases q with ⟨C', ρ⟩ | ⟨m, σ, ρU, ρV⟩
    · simp only [agmOMUFOracleImpl, StateT.run, StateT.mk] at hz
      split_ifs at hz with hg
      · obtain ⟨resp?, hresp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        change _ ∈ support (pure _ : ProbComp _) at hz
        rw [mem_support_pure_iff] at hz
        subst hz
        obtain ⟨u, -, rfl⟩ := (mem_support_atIssueSrv gen sk C' resp?).1 hresp
        refine AGMOMUFLog.consistent_append gen hlog _ ?_
        intro U' V' h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hg, u, rfl, rfl⟩
      · change _ ∈ support (pure _ : ProbComp _) at hz
        rw [mem_support_pure_iff] at hz
        subst hz
        refine AGMOMUFLog.consistent_append gen hlog _ ?_
        intro U' V' h
        cases h
    · simp only [agmOMUFOracleImpl, StateT.run, StateT.mk] at hz
      change _ ∈ support (pure _ : ProbComp _) at hz
      rw [mem_support_pure_iff] at hz
      subst hz
      exact hlog

omit hgen in
/-- From log positions to issuance positions: a log that is consistent entry by entry is
`ServerConsistent` as a run, the `k`-th issued pair sitting at the log position `i` with exactly
`k` issued pairs before it (`exists_index_of_getElem_filterMap`, `filterMap_take_eq_take`). -/
theorem OMUFTrace.serverConsistent_of_consistent (t : OMUFTrace F G)
    (hpp : t.pp = (t.sk.1 • t.H, t.sk.2.1 • gen, fun i => t.sk.2.2 i • gen))
    (hc : AGMOMUFLog.Consistent gen t.sk t.H t.pp t.log) : t.ServerConsistent gen := by
  refine ⟨hpp, fun k => ?_⟩
  have hk : (k : ℕ) < t.log.issued.length := by
    have h := k.2
    change (k : ℕ) < (AGMOMUFLog.tags t.log).length at h
    rwa [AGMOMUFLog.tags_eq_map_issued, List.length_map] at h
  obtain ⟨i, ⟨C', ρ, r?⟩, hi, hf, hlen⟩ := exists_index_of_getElem_filterMap
    (fun e : G × AGMRepr F 1 × Option (G × G) => e.2.2.map fun p => (e.2.1, p)) t.log k hk
  cases r? with
  | none => simp at hf
  | some p =>
    obtain ⟨U', V'⟩ := p
    have hf' : (ρ, (U', V')) = t.log.issued[(k : ℕ)] := by
      simpa using hf
    have hrepr : t.issuedRepr k = ρ := by
      simp only [OMUFTrace.issuedRepr, OMUFTrace.issuedReprs_eq_map_issued, List.getElem_map,
        ← hf']
    have htag : (AGMOMUFLog.tags t.log).get k = (U', V') := by
      simp only [List.get_eq_getElem, AGMOMUFLog.tags_eq_map_issued, List.getElem_map, ← hf']
    have htake : AGMOMUFLog.tags (t.log.take i) = (AGMOMUFLog.tags t.log).take k := by
      rw [AGMOMUFLog.tags_eq_map_issued, AGMOMUFLog.tags_eq_map_issued, ← List.map_take]
      congr 1
      have h := filterMap_take_eq_take
        (fun e : G × AGMRepr F 1 × Option (G × G) => e.2.2.map fun p => (e.2.1, p)) t.log i
      rw [hlen] at h
      exact h
    obtain ⟨hm, u, hU, hV⟩ := hc i C' ρ U' V' (by simpa using hi)
    refine ⟨C', ?_, u, ?_, ?_⟩
    · rw [hrepr, ← htake]
      exact hm
    · rw [htag]
      exact hU
    · rw [htag]
      exact hV

omit hgen in
/-- **Bridge, step 1.** A run in the support of `agmOMUFTrace` is server-consistent: induction
over the adversary's computation through `agmOMUFOracleImpl`, one invariant per Sign query, with
`mem_support_keygen` for the parameters. -/
theorem OMUFTrace.serverConsistent_of_mem_support (A : AGMOMUFAdversary F G 1)
    (t : OMUFTrace F G) (ht : t ∈ support (agmOMUFTrace gen secParam A)) :
    t.ServerConsistent gen := by
  obtain ⟨sk, H, pp, log, out⟩ := t
  unfold agmOMUFTrace at ht
  simp only [support_bind, Set.mem_iUnion] at ht
  obtain ⟨H', -, ⟨⟨x₀, xᵣ, x⟩, pp'⟩, hks, r, hr, hfin⟩ := ht
  change _ ∈ support (pure _ : ProbComp _) at hfin
  rw [mem_support_pure_iff] at hfin
  injection hfin with h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  have hpp := (mem_support_keygen (F := F) (G := G) H gen x₀ xᵣ x pp).1 hks
  have hcons := OracleComp.simulateQ_run_preservesInv (agmOMUFImpl gen secParam (x₀, xᵣ, x) H pp)
    (AGMOMUFLog.Consistent gen (x₀, xᵣ, x) H pp) (agmOMUFImpl_preservesInv gen secParam _ _ _)
    (A.run H pp) [] (AGMOMUFLog.consistent_nil gen _ _ _) r hr
  exact OMUFTrace.serverConsistent_of_consistent gen _ hpp hcons

/-- The group-side evaluation of a representation is the polynomial-side one at the point of
the run, whenever the issued tags the representation reads carry the commitment values `cs'`
(`V_j = (x₀ + xᵣ + c_j) • U_j`, the exponent of O24 Equation 18): the counterpart for the OMUF
game of `agmRepr_eval_eq_eval_toPoly`. -/
theorem OMUFTrace.eval_eq_smul_eval_toPolyAt (t : OMUFTrace F G)
    (hpp : t.pp = (t.sk.1 • t.H, t.sk.2.1 • gen, fun i => t.sk.2.2 i • gen))
    (ρ : AGMRepr F 1) (cs' : Fin t.arity → AGMPoly.P F t.arity)
    (htag : ∀ j : Fin t.arity, (j : ℕ) < ρ.uv.length →
      ((AGMOMUFLog.tags t.log).get j).2 =
        (t.sk.1 + t.sk.2.1 + MvPolynomial.eval (t.point gen) (cs' j)) •
          ((AGMOMUFLog.tags t.log).get j).1) :
    ρ.eval gen t.H t.pp.1 t.pp.2.1 t.pp.2.2 (AGMOMUFLog.tags t.log) =
      MvPolynomial.eval (t.point gen) ((ρ.toReprCoeffs t.arity).toPolyAt cs') • gen := by
  have hH := glog_smul (F := F) gen t.H
  simp only [OMUFTrace.point] at htag
  rw [hpp, AGMRepr.eval, AGMPoly.ReprCoeffs.eval_toPolyAt,
    sum_zipWith_eq_fin_sum_getD (fun (c : F × F) (t : G × G) => c.1 • t.1 + c.2 • t.2)
      ((0, 0) : F × F) ((0, 0) : G × G) (by intro t; simp only [zero_smul, add_zero]) ρ.uv]
  simp only [AGMRepr.toReprCoeffs, OMUFTrace.point, gamePoint, Fin.sum_univ_one]
  rw [add_smul, Finset.sum_smul]
  congr 1
  · generalize glog (F := F) gen t.H = η at hH ⊢
    rw [← hH]
    module
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : (j : ℕ) < ρ.uv.length
    · obtain ⟨u, hu⟩ := hgen.out.surjective ((AGMOMUFLog.tags t.log).get j).1
      have hu' : u • gen = ((AGMOMUFLog.tags t.log).get j).1 := hu
      rw [htag j hj, ← hu', glog_smul_self]
      module
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp

omit hgen in
/-- The `j`-th issued pair is `(U', V')` with `V' = (x₀ + xᵣ + c_j) • U'`, where `c_j` is the
value of the `j`-th commitment polynomial, given that this value names the commitment's
representation (`eval_point_cs` at `j`). The tag identity `eval_eq_smul_eval_toPolyAt` reads. -/
theorem OMUFTrace.tag_eq_of_eval (t : OMUFTrace F G) (ht : t.ServerConsistent gen)
    (j : Fin t.arity)
    (hj : MvPolynomial.eval (t.point gen) (t.cs j) • gen =
      (t.issuedRepr j).eval gen t.H t.pp.1 t.pp.2.1 t.pp.2.2 (AGMOMUFLog.tags t.log)) :
    ((AGMOMUFLog.tags t.log).get j).2 =
      (t.sk.1 + t.sk.2.1 + MvPolynomial.eval (t.point gen) (t.cs j)) •
        ((AGMOMUFLog.tags t.log).get j).1 := by
  obtain ⟨-, hk⟩ := ht
  obtain ⟨Cj, hmatchj, u, hU, hV⟩ := hk j
  have hCj : Cj = MvPolynomial.eval (t.point gen) (t.cs j) • gen := by
    have h := reprMatches_eval_append hmatchj ((AGMOMUFLog.tags t.log).drop j)
    rw [List.take_append_drop] at h
    rw [hj, h]
  rw [hV, hU, hCj]
  module

/-- **Bridge, step 2.** At the point of a server-consistent run, the `k`-th commitment polynomial
evaluates to the logarithm of the element the `k`-th issued representation names: strong induction
on `k` through `eval_toPolyAt`, the earlier slots entering through the server's answers
`V'_i = (x₀ + xᵣ + c_i) • U'_i` and the not-yet-issued slots through the `0` padding of
`toReprCoeffs`. -/
theorem OMUFTrace.eval_point_cs (t : OMUFTrace F G) (ht : t.ServerConsistent gen)
    (k : Fin t.arity) :
    MvPolynomial.eval (t.point gen) (t.cs k) • gen =
      (t.issuedRepr k).eval gen t.H t.pp.1 t.pp.2.1 t.pp.2.2 (AGMOMUFLog.tags t.log) := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    obtain ⟨hpp, hk⟩ := ht
    obtain ⟨C', hmatch, -⟩ := hk k
    have hlen : (t.issuedRepr k).uv.length = k := by
      rw [hmatch.1, List.length_take]
      have := AGMOMUFLog.tags_length_le t.log
      have := k.2
      change min (k : ℕ) t.arity = k
      omega
    -- the commitment polynomial reads the earlier ones and `0` from slot `k` on
    have hcs : t.cs k = ((t.issuedRepr k).toReprCoeffs t.arity).toPolyAt
        fun i => if (i : ℕ) < k then t.cs i else 0 := by
      rw [OMUFTrace.cs_eq_getElem]
      unfold OMUFTrace.commitPolys
      rw [AGMPoly.omufCommitPolys_getElem]
      simp only [List.getElem_map]
      rfl
    rw [hcs, ← t.eval_eq_smul_eval_toPolyAt gen hpp]
    intro j hj
    rw [hlen] at hj
    have hjk : j < k := hj
    rw [if_pos hj]
    exact t.tag_eq_of_eval gen ⟨hpp, hk⟩ j (ih j hjk)

/-- **Bridge, step 3.** A forgery with matching representations whose token satisfies the
verification equation has a forgery polynomial vanishing at the point of a server-consistent run
(O24 Equation 22): both representations are evaluated by `eval_toPolyAt` and step 2. -/
theorem OMUFTrace.eval_point_forgeryPoly (t : OMUFTrace F G) (ht : t.ServerConsistent gen)
    (e : AGMOMUFForgery F G 1)
    (hU : reprMatches e.reprU gen t.H t.pp.1 t.pp.2.1 t.pp.2.2 (AGMOMUFLog.tags t.log)
      e.token.1)
    (hV : reprMatches e.reprV gen t.H t.pp.1 t.pp.2.1 t.pp.2.2 (AGMOMUFLog.tags t.log)
      e.token.2)
    (hver : e.token.2 = (t.sk.1 + t.sk.2.1 + e.msg 0 * t.sk.2.2 0) • e.token.1) :
    MvPolynomial.eval (t.point gen)
      (AGMPoly.omufForgeryPoly t.cs (e.msg 0) (e.reprU.toReprCoeffs t.arity)
        (e.reprV.toReprCoeffs t.arity)) = 0 := by
  have hpp := ht.1
  have htag : ∀ (ρ : AGMRepr F 1) (j : Fin t.arity), (j : ℕ) < ρ.uv.length →
      ((AGMOMUFLog.tags t.log).get j).2 =
        (t.sk.1 + t.sk.2.1 + MvPolynomial.eval (t.point gen) (t.cs j)) •
          ((AGMOMUFLog.tags t.log).get j).1 :=
    fun _ j _ => t.tag_eq_of_eval gen ht j (t.eval_point_cs gen ht j)
  have hα := t.eval_eq_smul_eval_toPolyAt gen hpp e.reprU t.cs (htag e.reprU)
  have hβ := t.eval_eq_smul_eval_toPolyAt gen hpp e.reprV t.cs (htag e.reprV)
  rw [hU.2] at hα
  rw [hV.2] at hβ
  have key : MvPolynomial.eval (t.point gen)
      ((e.reprV.toReprCoeffs t.arity).toPolyAt t.cs) =
      (t.sk.1 + t.sk.2.1 + e.msg 0 * t.sk.2.2 0) *
        MvPolynomial.eval (t.point gen) ((e.reprU.toReprCoeffs t.arity).toPolyAt t.cs) := by
    apply hgen.out.injective
    change _ • gen = _ • gen
    rw [← hβ, hver, hα, mul_smul]
  rw [AGMPoly.omufForgeryPoly, MvPolynomial.eval_sub, MvPolynomial.eval_mul, key]
  simp only [AGMPoly.keyPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul, AGMPoly.x₀,
    AGMPoly.xᵣ, AGMPoly.x₁, MvPolynomial.eval_X, MvPolynomial.eval_C, OMUFTrace.point,
    gamePoint]
  ring

/-- **At the discrete-log point of a winning run, every forgery polynomial vanishes.** The
forgeries verify and their representations match, so the bridge gives the polynomial of each the
value `0` (`OMUFTrace.eval_point_forgeryPoly`). -/
theorem OMUFTrace.eval_point_of_wins (t : OMUFTrace F G) (ht : t.ServerConsistent gen)
    (hw : t.Wins gen secParam) : ∀ φ ∈ t.forgeryPolys, MvPolynomial.eval (t.point gen) φ = 0 := by
  intro φ hφ
  obtain ⟨e, he, hφe⟩ := List.mem_map.1 hφ
  obtain ⟨⟨-, -, hver⟩, hrepr⟩ := hw
  have hv := hver e.plain (List.mem_map_of_mem he)
  simp only [μCMZATCoreSyntax, verify, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hscalar : macScalar t.sk e.msg = t.sk.1 + t.sk.2.1 + e.msg 0 * t.sk.2.2 0 := by
    simp [macScalar, mul_comm]
  rw [← hφe]
  exact t.eval_point_forgeryPoly gen ht e (hrepr e he).1 (hrepr e he).2
    (by rw [← hscalar]; exact hv.2)

/-- The three cases cover a win: some forgery polynomial is nonzero
(`exists_forgeryPoly_ne_zero`) and vanishes at the run's discrete-log point, so it is not a
constant and has a variable (`cases_of_mem_vars`).

The vanishing at the discrete-log point is the evaluation bridge of this file
(`eval_point_forgeryPoly`), which needs `t` server-consistent
(`serverConsistent_of_mem_support`) and the verification equation of the forgery. -/
theorem omuf_cover (A : AGMOMUFAdversary F G 1) (t : OMUFTrace F G)
    (ht : t ∈ support (agmOMUFTrace gen secParam A)) (hw : t.Wins gen secParam) :
    t.CaseU gen secParam ∨ t.CaseEta gen secParam ∨ t.CaseX gen secParam := by
  obtain ⟨φ, hφ, hne⟩ := OMUFTrace.exists_forgeryPoly_ne_zero gen secParam t hw
  obtain ⟨e, he, hφe⟩ := List.mem_map.1 hφ
  have hcons := OMUFTrace.serverConsistent_of_mem_support gen secParam A t ht
  have hev : MvPolynomial.eval (t.point gen) φ = 0 :=
    t.eval_point_of_wins gen secParam hcons hw φ hφ
  have hw' := hw
  -- a nonzero polynomial with a root is not constant, so it has a variable
  have hvars : φ.vars.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, MvPolynomial.vars_eq_empty_iff_eq_C] at h
    apply hne
    rw [h] at hev ⊢
    rw [MvPolynomial.eval_C] at hev
    rw [hev, map_zero]
  obtain ⟨v, hvφ⟩ := hvars
  rcases AGMPoly.cases_of_mem_vars hvφ with h | h | h
  · exact Or.inl ⟨hw', φ, hφ, h⟩
  · exact Or.inr (Or.inl ⟨hw', φ, hφ, h⟩)
  · exact Or.inr (Or.inr ⟨hw', φ, hφ, h⟩)

end KVAC.Schemes.MicroCMZ
