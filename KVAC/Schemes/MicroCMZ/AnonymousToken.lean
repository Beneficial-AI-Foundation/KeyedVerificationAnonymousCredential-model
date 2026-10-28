/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Anonymity
import KVAC.Schemes.MicroCMZ.ATVariantPiIs
import KVAC.Schemes.MicroCMZ.OneMoreUnforgeability.Statements

/-!
# μCMZ_AT is an anonymous token (O24 §5.2, Theorem 5.3)

The statement of O24 Theorem 5.3 (p. 35) for the variant `μCMZ_AT` of Figure 9
whose issuance returns no `π_iu`, `μCMZATSyntax` of `ATVariantPiIs.lean`. An
anonymous token is correct, one-more unforgeable and anonymous (§3.4, p. 26),
and the theorem is the conjunction of the three clauses, each as the theorem
it derives from states it, p. 35 "From the above, and Theorem 5.11".

## Anonymity

Section 3.4 (p. 26) omits the definition of unlinkability and keeps "the
stronger anonymity properties", so the anonymity clause is Definition 4.4 on
the token as a credential, `μCMZATCredentialSyntax`, the issuance of Figure 9
without `π_iu` and the presentation of μCMZ. Its simulator
`μCMZATAnonSimulator` is the Theorem 5.8 simulator without its `π_iu`
simulator, since `Sim.I` has nothing to simulate at issuance.

The bound is `Adv^zk_cmz.p + Adv^ksnd_cmz.is`. The printed bound carries a
third term `Adv^zk_cmz.iu`, the cost of hybrid H1 of the Theorem 5.8 proof
(p. 41), which replaces the user's `π_iu` by a simulated one. The token's user
sends no `π_iu`, so H1 changes nothing and the term is vacuous. Errata item 18.

The condition of Remark 5.9, the hypotheses `Piu` to `his_p` of
`μCMZ_anonymity`, is not needed, for the following order of hybrids, which
the proof follows. First, replace the real `π_p` of every presentation by a
simulated one, with issuance honest and the credential real, so the
reduction `D'` holds the presentation witnesses and never runs the
extractor. Second, bound the event that the issuer's response is accepted and
the extraction from `π_is` fails or returns a wrong witness by the printed
`Adv^ksnd`, with the reduction `A''` stopping at the issuer's response. The
user's request is the commitment `C'` alone, `Sim.I₁` programs no oracle
point, and `anonGameRun` completes issuance before the distinguisher runs,
so the extractor reads the oracle table as it stands at the issuer's
response and no simulated proof precedes it. Third, couple the remaining
executions, the random `C'`, `U'`, `C_V` and `C⃗`, with the real ones.

## One-more unforgeability

The clause is on the game of Figure 6 at the oracle carrier, `OMUFGameRO`,
the game of the definition of §3.4, for the scheme with `π_is`. The bound is
that of Theorem 5.11, `omufBound`, plus one zero-knowledge term for `π_is`.

- *The bound.* Theorem 5.3 prints `Adv^2dl + q·Adv^dl + (q+5)/p`, the summary
  bound of the ePrint version of October 2024, which already disagreed with
  the proved theorem of that version in the 2-DL coefficient, and which no
  version proves. Theorem 5.11 (p. 43), from which Theorem 5.3 derives, prints
  `(q+6)/p + (q+1)·Adv^dl + 3·Adv^2dl + Adv^gapdl`. Errata item 19. The
  constants of `omufBound` are the printed ones and provisional until the
  constant audit of Track CMZ-OMUF (`Statements.lean`, *Constants and the
  extraction obligation*).
- *The `π_is` term.* The proof of Theorem 5.11 (p. 44) answers Sign with the
  bare `(U', V')` and analyzes the scheme without `π_is`, while Theorem 5.3 is
  about the scheme with it. The lifting lemma of issue #205 replaces each real
  `π_is` by a simulated one and pays `Adv^zk_cmz.is` once, since the §3.3
  zero-knowledge game answers as many `Prove_b` queries as the adversary
  makes. Errata item 7.
- *The model.* Theorem 5.11 holds in the algebraic group model, and the game
  of Theorem 5.11, `AGM_OMUFGame`, runs the core without `π_is`. The
  repository has no notion of an algebraic adversary for the scheme with
  `π_is`, whose issuer sends proofs that may carry group elements outside the
  basis of that game, so the clause quantifies over every adversary of
  Figure 6 and claims more than the paper proves. The proof of the clause
  needs the bridge from the game of Theorem 5.11 to the plain game on the
  core, which restricts the forger to algebraic behaviour, and an argument
  that the simulated `π_is` of the lifting lemma keeps the forger algebraic
  over the basis of that game. Recorded in `docs/DESIGN_ALTERNATIVES.md`,
  *Theorem 5.3 takes its clauses from Theorems 5.8 and 5.11*.

The reductions are declared with `sorry` bodies, as those of Theorem 5.11 are
(`Statements.lean`, *The reductions, named now and built with the proofs*).
The three of `omufBound` are the Theorem 5.11 reductions run on the forger
carried to the core by the lifting lemma, which attaches a simulated `π_is`
to each answer of the core and so depends on the simulator `simIs`, and
through the bridge. `omufPiIsZKAdversary` is the zero-knowledge adversary of
the lifting lemma, independent of the simulator, since its `Prove_b` oracle
supplies the proofs. Issue #205 defines the lifted forger and
`omufPiIsZKAdversary` against these signatures.

## The views of `ZKP_cmz.is` with a sampled crs

The one-more unforgeability game samples the crs `H` by `setup`, so the
zero-knowledge term is taken on the view `risNIZKPSampled`, whose setup is the
scheme's. The views of `Anonymity.lean` fix `H`, since Definition 4.4
quantifies over it pointwise. The four declarations `risNIZKPSampled`,
`risDecRelSampled`, `RisSimulator` and `risSimToZK` are those of the Theorem
5.10 setting (PR #244) and of its statement (PR #242); whichever merges second
keeps one copy.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework KVAC.Preliminaries ENNReal

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (HS : HashSpec)

/-! ## The token as a credential -/

section Scheme

variable (F)

/--
The anonymous token `μCMZ_AT` (O24 p. 35, Figure 9 without `π_iu`) as a
`KVACSyntax` at the oracle carrier, the scheme on which Definition 4.4 states
the anonymity clause of Theorem 5.3. Setup, key generation, the message and
key types are those of `μCMZCredKeyedSetup`. Issuance is that of
`μCMZATSyntax`, the user sends `C'` alone and the issuer answers
`(U', V', π_is)` without a check, and the predicate plays no part in it.
Presentation is that of `μCMZCredentialSyntax`, with `π_p` under the
predicate. The carriers are those of the credential, with
`IssueMsg _ := G`, the commitment `C'`.
-/
noncomputable def μCMZATCredentialSyntax (gen : G) (πis : RisProofSystem HS G F)
    (πp : ∀ n, RpProofSystem HS G F n) : KVACSyntax (OracleComp (ZKRO HS)) where
  toKeyedSetupSyntax := μCMZCredKeyedSetup F HS gen
  Pred := fun {_ n} _ => Policy F n
  holds := fun _ φ m => φ m
  trivialPred := fun _ => trivialPolicy
  holds_trivialPred := fun _ _ => rfl
  andPred := fun _ φ ψ => andPolicy φ ψ
  holds_andPred := fun _ _ _ _ => rfl
  DecidableEqPred := fun _ => inferInstance
  Cred := fun _ => Code G
  UsrState := fun {_ n} _ => F × G × Params G n
  IssueMsg := fun _ => G
  BlindCred := fun _ => G × G × πis.Proof
  PresentMsg := fun {_ n} _ => G × G × (Fin n → G) × (πp n).Proof
  DecidableEqPresentMsg := fun {_ n} _ =>
    have : DecidableEq ((Fin n → G) × (πp n).Proof) := inferInstance
    inferInstance
  exactPred := fun _ m => exactPolicy m
  holds_exactPred := fun _ m m' => exactPolicy_eq_true_iff m m'
  issueUsr₁ := fun _ pp m _ => atIssueUsr₁PiIs HS gen pp m
  issueSrv := fun H sk _ C' => atIssueSrvPiIs HS gen H πis sk C'
  issueUsr₂ := fun H st resp => credIssueUsr₂ HS H πis st resp
  presentUsr := fun {_ n} H pp m σ φ => credPresentUsr HS gen H (πp n) pp m σ φ
  presentSrv := fun {_ n} H sk φ ρ => credPresentSrv HS gen H (πp n) sk φ ρ

end Scheme

/-! ## The simulator -/

variable (gen : G) (πis : RisProofSystem HS G F) (πp : ∀ n, RpProofSystem HS G F n)

/--
The simulator of the anonymity clause of Theorem 5.3, `μCMZAnonSimulator` of
Theorem 5.8 (§5.4, p. 40) without the simulator of `ZKP_cmz.iu`. `Sim.I₁`
sends a random `C'`, which has the distribution of the honest commitment.
`Sim.I₂` and `Sim.P` are those of `μCMZAnonSimulator`, the extraction of `x₀`
from `π_is` and the simulated presentation.
-/
noncomputable def μCMZATAnonSimulator (simP : ∀ n, RpSimulator HS (πp n))
    (extIs : RisExtractor HS πis) :
    AnonSimulator HS (μCMZATCredentialSyntax F HS gen πis πp) where
  SimState := fun {_ n} _ => μCMZSimState (F := F) (G := G) n
  -- Sim.I₁. A random C', and no proof.
  simI₁ := fun _ pp _ => do
    let C' ← liftM ($ᵗ G)
    pure ((pp, C', (0 : F)), C')
  -- Sim.I₂. Check U' ≠ 0 and π_is, then extract (x₀, u).
  simI₂ := fun {_ _} H st σ' => do
    let (pp, C', _) := st
    let (U', V', π') := σ'
    if U' = 0 then
      pure none
    else
      let stmt : RisStmt G := (pp.1, C' + pp.2.1, U', V')
      let cache ← get
      let v ← simulateQ (zkROImpl HS) (πis.verify H stmt π')
      if v then
        let w? ← liftM (extIs H stmt π' cache)
        match w? with
        | some w =>
          if risRel gen H stmt w then pure (some (pp, C', w.1)) else pure none
        | none => pure none
      else
        pure none
  -- Sim.P. Random U' = u'•G, C_V and Cᵢ = γᵢ•G, Z from x₀, u' and the γᵢ, and a
  -- simulated π_p for (U', X, C, Z, φ').
  simP := fun {_ n} H st φ' => do
    let (pp, _, x₀) := st
    let u' ← liftM (uniformUnits F)
    let CV ← liftM ($ᵗ G)
    let γ ← liftM ($ᵗ (Fin n → F))
    let U' := u' • gen
    let C : Fin n → G := fun i => γ i • gen
    let Z := x₀ • U' + u' • pp.2.1 + (∑ i, γ i • pp.2.2 i) - CV
    let π ← simP n H (U', pp.2.2, C, Z, φ')
    pure (U', CV, C, π)

/-! ## `ZKP_cmz.is` with the crs sampled by `setup` -/

/-- `ZKP_cmz.is` as a §3.3 proof system for `R_cmz.is` (O24 Eq. 10), with the crs
sampled as the scheme's setup samples it. -/
noncomputable def risNIZKPSampled (n : ℕ) (π : RisProofSystem HS G F) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun secParam => liftM ((μCMZBaseMACSyntax F gen).setup secParam n))
    (fun H' x w => risRel gen H' x w = true)

/-- The relation of `risNIZKPSampled` is decidable. -/
abbrev risDecRelSampled (n : ℕ) (π : RisProofSystem HS G F) :
    (risNIZKPSampled HS gen n π).DecidableRelation :=
  fun H' x w => show Decidable (risRel gen H' x w = true) from inferInstance

/-- The zero-knowledge simulator of `ZKP_cmz.is`, a function of the crs `H : G`. -/
abbrev RisSimulator (π : RisProofSystem HS G F) : Type :=
  G → RisStmt G → StateT HS.Cache ProbComp π.Proof

/-- A `RisSimulator` as the `ZKSimulator` of `risNIZKPSampled`. -/
def risSimToZK (n : ℕ) (π : RisProofSystem HS G F) (s : RisSimulator HS π) :
    ZKSimulator HS (risNIZKPSampled HS gen n π) :=
  fun {_} crs x => s crs x

/-! ## The Sign budget at the oracle carrier -/

/-- The Sign query as a predicate on the queries of an `OMUFAdversaryRO`, the
random oracle included, the one `IsQueryBoundP` counts for the budget `q` of
Theorem 5.3, "the number of queries to the issuance oracle". -/
def OMUFQueryRO.isSign {tok : ATSyntax (OracleComp (ZKRO HS))} {secParam n : ℕ}
    {crs : tok.Crs secParam n} : (ℕ ⊕ HS.Dom) ⊕ OMUFQuery tok crs → Prop
  | .inl _ => False
  | .inr (.sign _) => True
  | .inr (.verify _ _) => False

/-- `IsQueryBoundP` needs the predicate decidable. -/
instance OMUFQueryRO.instDecidablePredIsSign {tok : ATSyntax (OracleComp (ZKRO HS))}
    {secParam n : ℕ} {crs : tok.Crs secParam n} :
    DecidablePred (OMUFQueryRO.isSign HS (tok := tok) (secParam := secParam) (n := n) (crs := crs))
  | .inl _ => isFalse id
  | .inr (.sign _) => isTrue trivial
  | .inr (.verify _ _) => isFalse id

/-! ## The reductions, named now and built with the proofs

Each takes a one-more forger of the scheme with `π_is` in the game of Figure 6
at the oracle carrier. The first three are the reductions of Theorem 5.11,
`omufDLReduction`, `omufTwoDLReduction` and `omufGapDLReduction` through
`omufToN1`, run on the forger carried to the core by the lifting lemma of
issue #205, which answers the forger's Sign queries with the core's
`(U', V')` and a `π_is` from the simulator `simIs`, and by the bridge from the
game of Theorem 5.11 to the plain game. They take `simIs` for that reason.
The fourth is the zero-knowledge adversary of the lifting lemma, which takes
its proofs from the `Prove_b` oracle and so no simulator. As in
`Statements.lean`, the generator and its bijectivity fact are explicit
binders, and the `sorry` inhabits the whole function type. -/

/-- The discrete-log reduction of the one-more unforgeability clause of Theorem
5.3, for the simulator `simIs` of `π_is`, the Sign budget `q` and `n`
attributes. -/
noncomputable def omufATDLReduction :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))]
      (πis : RisProofSystem HS G F), RisSimulator HS πis → ∀ (n q : ℕ),
      OMUFAdversaryRO HS (μCMZATSyntax F HS gen πis) → DiffieHellman.DLogAdversary F G :=
  sorry

/-- The 2-DL reduction of the one-more unforgeability clause of Theorem 5.3,
for the simulator `simIs` of `π_is` and `n` attributes. -/
noncomputable def omufATTwoDLReduction :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))]
      (πis : RisProofSystem HS G F), RisSimulator HS πis → ∀ (n : ℕ),
      OMUFAdversaryRO HS (μCMZATSyntax F HS gen πis) → QDLogAdversary 2 F G :=
  sorry

/-- The gap-DL reduction of the one-more unforgeability clause of Theorem 5.3,
the collision case of the general `n` argument, for the simulator `simIs` of
`π_is` and `n` attributes. -/
noncomputable def omufATGapDLReduction :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))]
      (πis : RisProofSystem HS G F), RisSimulator HS πis → ∀ (n : ℕ),
      OMUFAdversaryRO HS (μCMZATSyntax F HS gen πis) → GapDLogAdversary F G :=
  sorry

/-- The zero-knowledge adversary of `ZKP_cmz.is` of the lifting lemma (issue
#205, errata item 7), from a one-more forger of the scheme with `π_is`. It runs
the forger with the issuer's proofs taken from its `Prove_b` oracle, and
answers whether the forger wins. -/
noncomputable def omufPiIsZKAdversary :
    ∀ (gen : G) [Fact (Function.Bijective (fun x : F => x • gen))]
      (πis : RisProofSystem HS G F) (n : ℕ),
      OMUFAdversaryRO HS (μCMZATSyntax F HS gen πis) →
        ZKAdversary HS (risNIZKPSampled HS gen n πis) :=
  sorry

/-! ## Theorem 5.3 -/

/--
**O24 Theorem 5.3.** For a generator `gen` and proof systems `πis` for
`R_cmz.is` and `πp n` for `R_cmz.p`, with `πis` perfectly complete, μCMZ_AT is
an anonymous token (§3.4). Three clauses.

*Correctness.* `μCMZATSyntax` satisfies `ATSyntax.CorrectRO`, the theorem
`μCMZAT_correctRO`.

*Anonymity.* For `H ≠ 0`, `(sk, pp) ∈ [K(H)]` and `φ(m) = 1`, the anonymity
advantage of `μCMZATCredentialSyntax` from the empty random-oracle table with
respect to `μCMZATAnonSimulator` is at most the zero-knowledge advantage of
`ZKP_cmz.p` plus the knowledge-soundness advantage of `ZKP_cmz.is`, for
reductions `D'` and `A''`. The printed bound has a third term `Adv^zk_cmz.iu`,
errata item 18 (module docstring, *Anonymity*).

*One-more unforgeability.* For `0 < n` and a forger `A` of the game of Figure
6 at the oracle carrier with at most `q` Sign queries, the advantage of `A` is
at most `omufBound` of Theorem 5.11, with the discrete-log, 2-DL and gap-DL
advantages of the named reductions, plus the zero-knowledge advantage of
`ZKP_cmz.is` for `omufPiIsZKAdversary`. The printed bound is the summary
bound of the October 2024 version, errata item 19, the `π_is` term is errata
item 7, and the clause quantifies over every adversary where the paper
restricts to algebraic ones (module docstring, *One-more unforgeability*).

The three clauses are inequalities and a correctness predicate at fixed `F`,
`G`, `secParam` and `n`. The clause "for n = poly(λ) attributes", with
negligible advantages and efficient reductions, is the asymptotic statement
left to issue #148, as for Theorems 5.2, 5.8 and 5.10. The credential
`μCMZATCredentialSyntax` and the token `μCMZATSyntax` share their setup, key
generation and issuance moves by definition, so the anonymity clause speaks
of the same issuance as the other two.
-/
theorem μCMZAT_anonymous_token [Fact (Function.Bijective (fun x : F => x • gen))]
    (hgen : gen ≠ 0) (simIs : RisSimulator HS πis) (simP : ∀ n, RpSimulator HS (πp n))
    (extIs : RisExtractor HS πis)
    (his : πis.CompleteRO HS (fun k => (μCMZBaseMACSyntax F gen).setup k 0)
      (fun H x w => risRel (F := F) gen H x w)) :
    -- Correctness.
    (μCMZATSyntax F HS gen πis).CorrectRO HS ∧
    -- Anonymity, Definition 4.4 with the Theorem 5.8 simulator without `π_iu`.
    (∀ {secParam n : ℕ} (H : G), H ≠ 0 → ∀ (sk : Key F n) (pp : Params G n),
      (sk, pp) ∈ support (keygen (F := F) (n := n) H gen) →
      ∀ (m : Fin n → F) (φ : Policy F n), φ m = true →
      ∀ (issuer : AnonIssuer HS (μCMZATCredentialSyntax F HS gen πis πp))
        (D : AnonDistinguisher HS (μCMZATCredentialSyntax F HS gen πis πp) issuer.StA),
      ∃ (D' : ZKAdversary HS (rpNIZKP HS gen H (πp n)))
        (A'' : KSNDAdversary HS (risNIZKP HS gen H πis)),
        AnonAdv HS (μCMZATCredentialSyntax F HS gen πis πp) issuer D
            (μCMZATAnonSimulator HS gen πis πp simP extIs)
            (secParam := secParam) (n := n) H sk pp m φ ∅ ≤
          ZKAdv HS (rpNIZKP HS gen H (πp n)) (rpDecRel HS gen H (πp n)) D'
              (rpSimToZK HS gen H (πp n) (simP n)) secParam
          + (KSNDAdv HS (risNIZKP HS gen H πis)
              (TraceExtractor.toKSND (risExtToTrace HS gen H πis extIs)) A''
              (risDecRel HS gen H πis) secParam).toReal) ∧
    -- One-more unforgeability, Figure 6 at the oracle carrier with the Theorem
    -- 5.11 bound and the `π_is` term.
    (∀ {n : ℕ}, 0 < n → ∀ (secParam : ℕ)
      (A : OMUFAdversaryRO HS (μCMZATSyntax F HS gen πis)) (q : ℕ),
      (∀ (H : G) (pp : Params G n),
        IsQueryBoundP (A.run (secParam := secParam) (n := n) H pp)
          (OMUFQueryRO.isSign HS) q) →
      OMUFAdvRO HS (μCMZATSyntax F HS gen πis) A secParam n ≤
        omufBound F q (dlogAdv gen (omufATDLReduction HS gen πis simIs n q A))
          (twoDlogAdv gen (omufATTwoDLReduction HS gen πis simIs n A))
          (gapDlogAdv gen (omufATGapDLReduction HS gen πis simIs n A))
        + ENNReal.ofReal (ZKAdv HS (risNIZKPSampled HS gen n πis)
            (risDecRelSampled HS gen n πis) (omufPiIsZKAdversary HS gen πis n A)
            (risSimToZK HS gen n πis simIs) secParam)) := by
  sorry

end KVAC.Schemes.MicroCMZ
