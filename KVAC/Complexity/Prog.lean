/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Core.Group
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.Coercions.Add

/-!
# A language of programs with a running time polynomial in λ

O24 states its security properties for p.p.t. adversaries. §3 (p. 24) writes
the length of the random coins of a p.p.t. algorithm as A.rl(λ), and it writes
an interaction as that of "the interactive Turing machine A" with a machine B.
An `OracleComp` computation has no running time, so no predicate on it
expresses the p.p.t. class (issue #240).

This file defines a first-order language whose terms are programs.

- `Ty` is the type of sorts. A program mentions no field and no group, so one
  term runs at the group of every security parameter.
- `Expr` is the type of pure expressions, and `Prog` is the type of programs
  over a signature `Sig` of oracles. Variables are de Bruijn indices. A
  continuation is a term, not a Lean function, so a program computes only
  through the constructors.
- `Prog.timePoly` computes the running time polynomial from the syntax. Each
  field operation, group operation, query and draw has unit cost. A loop
  carries its iteration count as a polynomial in λ.
- `Prog.coinPoly` bounds the fair coins, and `Prog.CoinOnly` holds for a program
  with no exact draw from the scalar field.
- `Prog.interp` maps a program to an `OracleComp` computation over
  `unifSpec + S.spec F G`, the carrier of the adversaries of the repository.
- `Prog.isQueryBoundP_interp` bounds the oracle queries of the interpretation
  by the running time polynomial at λ.

A group value arises only as a variable, as an oracle answer, as zero or as
the result of a group operation. No constructor maps a scalar to a group
element.

The language has a fair coin, `Prog.coin`, and an exact draw from the scalar
field, `Prog.sampleF`. Figure 9 (p. 34) draws `s ←$ ℤ_p` exactly. Part A6.6 of
`docs/findings/FINDINGS_AND_LESSONS.md` records the decision and
`KVAC/Preliminaries/CoinTape.lean` the reason.
-/

namespace KVAC.Complexity

open OracleSpec OracleComp Polynomial

/-- The sorts of the language. The sorts `scalar` and `group` are abstract, so a term
mentions no field and no group. -/
inductive Ty : Type
  | unit | bool | scalar | group
  | prod (a b : Ty)
  | option (a : Ty)
  | list (a : Ty)
  deriving DecidableEq

/-- The values of a sort at the scalar field `F` and the group `G`. -/
@[reducible] def Ty.interp (F G : Type) : Ty → Type
  | .unit => Unit
  | .bool => Bool
  | .scalar => F
  | .group => G
  | .prod a b => a.interp F G × b.interp F G
  | .option a => Option (a.interp F G)
  | .list a => List (a.interp F G)

/-- A typing context, the list of the sorts of the variables in scope. -/
abbrev Ctx : Type := List Ty

/-- A variable of sort `τ` in the context `Γ`, as a de Bruijn index. -/
inductive Var : Ctx → Ty → Type
  | here {Γ : Ctx} {τ : Ty} : Var (τ :: Γ) τ
  | there {Γ : Ctx} {τ σ : Ty} : Var Γ τ → Var (σ :: Γ) τ

/-- An environment for the context `Γ`, one value per variable. -/
def Env (F G : Type) : Ctx → Type
  | [] => Unit
  | τ :: Γ => τ.interp F G × Env F G Γ

/-- The value of a variable in an environment. -/
def Env.get {F G : Type} : {Γ : Ctx} → {τ : Ty} → Env F G Γ → Var Γ τ → τ.interp F G
  | _ :: _, _, ρ, .here => ρ.1
  | _ :: _, _, ρ, .there v => Env.get ρ.2 v

/-- A signature of oracles indexed by `ι`, with the sort of the query and the sort of the
answer of each oracle. -/
structure Sig (ι : Type) where
  /-- The sort of the query of an oracle. -/
  dom : ι → Ty
  /-- The sort of the answer of an oracle. -/
  cod : ι → Ty

/-- The oracle specification of a signature at the field `F` and the group `G`. -/
def Sig.spec {ι : Type} (S : Sig ι) (F G : Type) : OracleSpec (Σ i, (S.dom i).interp F G) :=
  fun q => (S.cod q.1).interp F G

/-- The pure expressions of sort `τ` in the context `Γ`. The constructor `nat` is the only
scalar constant and `zeroG` the only group constant. -/
inductive Expr : Ctx → Ty → Type
  | var {Γ : Ctx} {τ : Ty} : Var Γ τ → Expr Γ τ
  | unit {Γ : Ctx} : Expr Γ .unit
  | bool {Γ : Ctx} (b : Bool) : Expr Γ .bool
  | not {Γ : Ctx} : Expr Γ .bool → Expr Γ .bool
  | and {Γ : Ctx} : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | nat {Γ : Ctx} (n : ℕ) : Expr Γ .scalar
  | addF {Γ : Ctx} : Expr Γ .scalar → Expr Γ .scalar → Expr Γ .scalar
  | mulF {Γ : Ctx} : Expr Γ .scalar → Expr Γ .scalar → Expr Γ .scalar
  | negF {Γ : Ctx} : Expr Γ .scalar → Expr Γ .scalar
  | invF {Γ : Ctx} : Expr Γ .scalar → Expr Γ .scalar
  | eqF {Γ : Ctx} : Expr Γ .scalar → Expr Γ .scalar → Expr Γ .bool
  | zeroG {Γ : Ctx} : Expr Γ .group
  | addG {Γ : Ctx} : Expr Γ .group → Expr Γ .group → Expr Γ .group
  | negG {Γ : Ctx} : Expr Γ .group → Expr Γ .group
  | smul {Γ : Ctx} : Expr Γ .scalar → Expr Γ .group → Expr Γ .group
  | eqG {Γ : Ctx} : Expr Γ .group → Expr Γ .group → Expr Γ .bool
  | pair {Γ : Ctx} {σ τ : Ty} : Expr Γ σ → Expr Γ τ → Expr Γ (.prod σ τ)
  | fst {Γ : Ctx} {σ τ : Ty} : Expr Γ (.prod σ τ) → Expr Γ σ
  | snd {Γ : Ctx} {σ τ : Ty} : Expr Γ (.prod σ τ) → Expr Γ τ
  | none {Γ : Ctx} {τ : Ty} : Expr Γ (.option τ)
  | some {Γ : Ctx} {τ : Ty} : Expr Γ τ → Expr Γ (.option τ)
  | nil {Γ : Ctx} {τ : Ty} : Expr Γ (.list τ)
  | cons {Γ : Ctx} {τ : Ty} : Expr Γ τ → Expr Γ (.list τ) → Expr Γ (.list τ)

/-- The number of constructors of an expression, its running time at unit cost. -/
def Expr.size : {Γ : Ctx} → {τ : Ty} → Expr Γ τ → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .zeroG
  | _, _, .none | _, _, .nil => 1
  | _, _, .not a | _, _, .negF a | _, _, .invF a | _, _, .negG a | _, _, .fst a
  | _, _, .snd a | _, _, .some a => a.size + 1
  | _, _, .and a b | _, _, .addF a b | _, _, .mulF a b | _, _, .eqF a b | _, _, .addG a b
  | _, _, .smul a b | _, _, .eqG a b | _, _, .pair a b | _, _, .cons a b => a.size + b.size + 1

section Semantics

variable {F : Type} [Field F] [DecidableEq F]
variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The value of an expression in an environment. The case `negF` subtracts from zero,
since the search for the instance `Neg F` exceeds the default limit in this context. -/
def Expr.eval : {Γ : Ctx} → {τ : Ty} → Expr Γ τ → Env F G Γ → τ.interp F G
  | _, _, .var v, ρ => ρ.get v
  | _, _, .unit, _ => ()
  | _, _, .bool b, _ => b
  | _, _, .not a, ρ => !(a.eval ρ)
  | _, _, .and a b, ρ => a.eval ρ && b.eval ρ
  | _, _, .nat n, _ => (n : F)
  | _, _, .addF a b, ρ => (a.eval ρ : F) + b.eval ρ
  | _, _, .mulF a b, ρ => (a.eval ρ : F) * b.eval ρ
  | _, _, .negF a, ρ => (0 : F) - a.eval ρ
  | _, _, .invF a, ρ => (a.eval ρ : F)⁻¹
  | _, _, .eqF a b, ρ => decide ((a.eval ρ : F) = b.eval ρ)
  | _, _, .zeroG, _ => (0 : G)
  | _, _, .addG a b, ρ => (a.eval ρ : G) + b.eval ρ
  | _, _, .negG a, ρ => Neg.neg (α := G) (a.eval ρ)
  | _, _, .smul a b, ρ => (a.eval ρ : F) • (b.eval ρ : G)
  | _, _, .eqG a b, ρ => decide ((a.eval ρ : G) = b.eval ρ)
  | _, _, .pair a b, ρ => (a.eval ρ, b.eval ρ)
  | _, _, .fst a, ρ => (a.eval ρ).1
  | _, _, .snd a, ρ => (a.eval ρ).2
  | _, _, .none, _ => Option.none
  | _, _, .some a, ρ => Option.some (a.eval ρ)
  | _, _, .nil, _ => []
  | _, _, .cons a b, ρ => a.eval ρ :: b.eval ρ

end Semantics

/-- The programs of sort `τ` in the context `Γ` over the signature `S`.

- `ret` returns the value of an expression.
- `bind` runs a program and binds its result in a second program.
- `query` queries an oracle of the signature.
- `coin` draws a fair coin, and `sampleF` draws an exactly uniform scalar.
- `ite`, `caseOption` and `caseList` branch on a Boolean, an option and a list.
- `loop b e body` iterates `body` on a state that starts at `e`. The number of iterations
  is the value of the polynomial `b` at the security parameter. -/
inductive Prog {ι : Type} (S : Sig ι) : Ctx → Ty → Type
  | ret {Γ : Ctx} {τ : Ty} : Expr Γ τ → Prog S Γ τ
  | bind {Γ : Ctx} {σ τ : Ty} : Prog S Γ σ → Prog S (σ :: Γ) τ → Prog S Γ τ
  | query {Γ : Ctx} (i : ι) : Expr Γ (S.dom i) → Prog S Γ (S.cod i)
  | coin {Γ : Ctx} : Prog S Γ .bool
  | sampleF {Γ : Ctx} : Prog S Γ .scalar
  | ite {Γ : Ctx} {τ : Ty} : Expr Γ .bool → Prog S Γ τ → Prog S Γ τ → Prog S Γ τ
  | caseOption {Γ : Ctx} {σ τ : Ty} :
      Expr Γ (.option σ) → Prog S Γ τ → Prog S (σ :: Γ) τ → Prog S Γ τ
  | caseList {Γ : Ctx} {σ τ : Ty} :
      Expr Γ (.list σ) → Prog S Γ τ → Prog S (σ :: .list σ :: Γ) τ → Prog S Γ τ
  | loop {Γ : Ctx} {σ : Ty} (b : ℕ[X]) : Expr Γ σ → Prog S (σ :: Γ) σ → Prog S Γ σ

/-- The running time polynomial of a program, computed from its syntax. A branch counts
both of its arms, so the polynomial is an upper bound. -/
noncomputable def Prog.timePoly {ι : Type} {S : Sig ι} : {Γ : Ctx} → {τ : Ty} → Prog S Γ τ → ℕ[X]
  | _, _, .ret e => C e.size
  | _, _, .bind p q => p.timePoly + q.timePoly
  | _, _, .query _ e => C (e.size + 1)
  | _, _, .coin => 1
  | _, _, .sampleF => 1
  | _, _, .ite c t e => C (c.size + 1) + t.timePoly + e.timePoly
  | _, _, .caseOption e n s => C (e.size + 1) + n.timePoly + s.timePoly
  | _, _, .caseList e n c => C (e.size + 1) + n.timePoly + c.timePoly
  | _, _, .loop b e body => C (e.size + 1) + b * body.timePoly

/-- The polynomial that bounds the fair coins of a program, the length A.rl(λ) of the coin
tape of O24 §3 (p. 24) for a program with no exact draw. -/
noncomputable def Prog.coinPoly {ι : Type} {S : Sig ι} : {Γ : Ctx} → {τ : Ty} → Prog S Γ τ → ℕ[X]
  | _, _, .ret _ | _, _, .query _ _ | _, _, .sampleF => 0
  | _, _, .coin => 1
  | _, _, .bind p q => p.coinPoly + q.coinPoly
  | _, _, .ite _ t e => t.coinPoly + e.coinPoly
  | _, _, .caseOption _ n s => n.coinPoly + s.coinPoly
  | _, _, .caseList _ n c => n.coinPoly + c.coinPoly
  | _, _, .loop b _ body => b * body.coinPoly

/-- A program is coin-only when it has no exact draw from the scalar field. The coin-only
programs draw their randomness from fair coins alone, as the coin tape of O24 §3 (p. 24)
and of Definition 7.1 (p. 58) prints it. -/
def Prog.CoinOnly {ι : Type} {S : Sig ι} : {Γ : Ctx} → {τ : Ty} → Prog S Γ τ → Prop
  | _, _, .ret _ | _, _, .query _ _ | _, _, .coin => True
  | _, _, .sampleF => False
  | _, _, .bind p q => p.CoinOnly ∧ q.CoinOnly
  | _, _, .ite _ t e => t.CoinOnly ∧ e.CoinOnly
  | _, _, .caseOption _ n s => n.CoinOnly ∧ s.CoinOnly
  | _, _, .caseList _ n c => n.CoinOnly ∧ c.CoinOnly
  | _, _, .loop _ _ body => body.CoinOnly

/-- The iteration of a monadic step `k` times. -/
def iterM {m : Type → Type} [Monad m] {α : Type} (f : α → m α) : ℕ → α → m α
  | 0, a => pure a
  | k + 1, a => f a >>= iterM f k

section Interp

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]
variable {ι : Type} {S : Sig ι}

/-- The interpretation of a program at the security parameter `secParam`, the field `F` and
the group `G`. The oracles of the signature are the right summand of the specification, and
the coin and the exact draw use the left summand `unifSpec`. -/
def Prog.interp (secParam : ℕ) :
    {Γ : Ctx} → {τ : Ty} → Prog S Γ τ → Env F G Γ →
      OracleComp (unifSpec + S.spec F G) (τ.interp F G)
  | _, _, .ret e, ρ => pure (e.eval ρ)
  | _, _, .bind p q, ρ => p.interp secParam ρ >>= fun a => q.interp secParam (a, ρ)
  | _, _, .query i e, ρ =>
      (unifSpec + S.spec F G).query (Sum.inr ⟨i, e.eval ρ⟩)
  | _, _, .coin, _ => liftComp ($ᵗ Bool) _
  | _, _, .sampleF, _ => liftComp ($ᵗ F) _
  | _, _, .ite c t e, ρ => if c.eval ρ then t.interp secParam ρ else e.interp secParam ρ
  | _, _, .caseOption e n s, ρ =>
      match e.eval ρ with
      | Option.none => n.interp secParam ρ
      | Option.some a => s.interp secParam (a, ρ)
  | _, _, .caseList e n c, ρ =>
      match e.eval ρ with
      | [] => n.interp secParam ρ
      | a :: l => c.interp secParam (a, l, ρ)
  | _, _, .loop b e body, ρ =>
      iterM (fun s => body.interp secParam (s, ρ)) (b.eval secParam) (e.eval ρ)

end Interp

section QueryBound

variable {ι : Type} {S : Sig ι}

/-- The queries of `Prog.interp` to the oracles of the signature, as opposed to the queries
to its coin oracle. -/
def IsOracleQuery {F G : Type} (t : ℕ ⊕ (Σ i, (S.dom i).interp F G)) : Prop := t.isRight = true

instance {F G : Type} : DecidablePred (IsOracleQuery (F := F) (G := G) (S := S)) :=
  fun t => inferInstanceAs (Decidable (t.isRight = true))

/-- A computation over the coin oracle alone makes no query to the oracles of the
signature. -/
lemma isQueryBoundP_liftComp_probComp {F G : Type} {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (unifSpec + S.spec F G))
      (IsOracleQuery (F := F) (G := G) (S := S)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      simp only [liftComp_bind, liftComp_query]
      change IsQueryBoundP
        (liftM ((unifSpec + S.spec F G).query (Sum.inl t)) >>= fun u =>
          liftComp (mx u) (unifSpec + S.spec F G)) _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [IsOracleQuery]), fun u => by simpa [IsOracleQuery] using ih u⟩

/-- An iteration of `k` steps makes at most `k * m` queries that satisfy `p` when each step
makes at most `m`. -/
lemma isQueryBoundP_iterM {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (p : ι' → Prop) [DecidablePred p] (f : α → OracleComp spec α) (m : ℕ)
    (hf : ∀ a, IsQueryBoundP (f a) p m) (k : ℕ) (a : α) :
    IsQueryBoundP (iterM f k a) p (k * m) := by
  induction k generalizing a with
  | zero => simp [iterM]
  | succ k ih =>
      have h := isQueryBoundP_bind (p := p) (hf a) (fun x _ => ih x)
      simpa [iterM, Nat.succ_mul, Nat.add_comm] using h

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The interpretation of a program at the security parameter λ makes at most
`P.timePoly.eval λ` queries to the oracles of the signature. -/
theorem Prog.isQueryBoundP_interp (secParam : ℕ) {Γ : Ctx} {τ : Ty} (P : Prog S Γ τ)
    (ρ : Env F G Γ) :
    IsQueryBoundP (P.interp secParam ρ) (IsOracleQuery (F := F) (G := G) (S := S))
      (P.timePoly.eval secParam) := by
  induction P with
  | ret e => simp [Prog.interp]
  | bind p q ihp ihq =>
      simp only [Prog.interp, Prog.timePoly, eval_add]
      exact isQueryBoundP_bind (ihp ρ) (fun a _ => ihq (a, ρ))
  | query i e =>
      simp only [Prog.interp, Prog.timePoly, eval_C]
      exact (isQueryBoundP_query_iff (spec := unifSpec + S.spec F G) _
        (Sum.inr ⟨i, e.eval ρ⟩) _).mpr fun _ => Nat.succ_pos _
  | coin => exact (isQueryBoundP_liftComp_probComp _).mono (Nat.zero_le _)
  | sampleF => exact (isQueryBoundP_liftComp_probComp _).mono (Nat.zero_le _)
  | ite c t e iht ihe =>
      simp only [Prog.interp, Prog.timePoly, eval_add, eval_C]
      split
      · exact (iht ρ).mono (by omega)
      · exact (ihe ρ).mono (by omega)
  | caseOption e n s ihn ihs =>
      simp only [Prog.interp, Prog.timePoly, eval_add, eval_C]
      split
      · exact (ihn ρ).mono (by omega)
      · exact (ihs _).mono (by omega)
  | caseList e n c ihn ihc =>
      simp only [Prog.interp, Prog.timePoly, eval_add, eval_C]
      split
      · exact (ihn ρ).mono (by omega)
      · exact (ihc _).mono (by omega)
  | loop b e body ih =>
      simp only [Prog.interp, Prog.timePoly, eval_add, eval_C, eval_mul]
      exact (isQueryBoundP_iterM _ _ _ (fun s => ih (s, ρ)) _ _).mono (by omega)

end QueryBound

section Example

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The program that draws a scalar `s` and returns `s • X`, for the variable `X`. Its
interpretation is the draw followed by the scalar multiplication, and its running time
polynomial is the constant 4. -/
example (S : Sig Empty) (secParam : ℕ) (X : G) :
    (Prog.bind (S := S) (Γ := [.group]) .sampleF
        (.ret (.smul (.var .here) (.var (.there .here))))).interp secParam
        (show Env F G [.group] from (X, ()))
      = liftComp ($ᵗ F) _ >>= fun s => pure (s • X) := by
  simp [Prog.interp, Expr.eval, Env.get]

example (S : Sig Empty) :
    (Prog.bind (S := S) (Γ := [.group]) .sampleF
        (.ret (.smul (.var .here) (.var (.there .here))))).timePoly = 4 := by
  simp only [Prog.timePoly, Expr.size]
  norm_num

end Example

end KVAC.Complexity
