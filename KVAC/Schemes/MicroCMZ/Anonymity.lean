/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Christiano Braga
-/
import KVAC.Schemes.MicroCMZ.Credential
import KVAC.Framework.Anonymity
import KVAC.Core.NIZKP.Composition

/-!
# Anonymity of μCMZ (O24 §5.4, Theorem 5.8)

The statement of O24 Theorem 5.8 for `μCMZCredentialSyntax` of Figure 9, with
the simulator `Sim = (Sim.I, Sim.P)` of its proof (§5.4, pp. 40 to 41). The
proof is deferred. The sections below hold, in order, the three proof systems
as §3.3 objects, the simulators and the extractor they provide, the simulation
oracle of Remark 5.9, the simulator of Theorem 5.8, and the theorem.

## Departures from the printed text

The statement and the simulator depart from the printed text in seven points.
Each is a correction of the paper or a hypothesis the paper uses without
stating. `docs/DESIGN_ALTERNATIVES.md` records the decisions and
`docs/presentations/rolf-status/errata.md` the errors.

### 1. The extractor takes the trace of the run, not the adversary

**Printed.** The §3.3 extractor "takes as input the random coins and the code
of the p.p.t. adversary A" (p. 26), and `KSNDExtractor` takes the adversary
value. `Sim.I` "invokes the extractor" on `π_is` (p. 40).

**Gap.** `Sim.I` runs inside the anonymity game, where it holds the issuer's
message and the oracle table and nothing else, and Definition 4.4 (p. 30)
fixes `Sim` before the adversary. So `Sim.I` has no adversary to hand to the
extractor, and the paper does not say how it is invoked.

**Formalized.** The simulator takes a `TraceExtractor` of
`Core/NIZKP/Composition`, a function of the crs, the statement, the proof and
the oracle table. `toKSND` makes it a `KSNDExtractor`, so the printed
`Adv^ksnd` applies to it. The hypothesis is stronger than the printed one. The
lemma `KnowledgeSound.of_trace` states that it implies the printed one, and
the paper's own extractors satisfy it (§5.5, p. 42, §9, p. 77).

### 2. `Z` carries the term `xᵣ•U'`

**Printed.** The server of Figure 9 (p. 34) recomputes
`Z = (x₀ + xᵣ)•U' + Σᵢ xᵢ•Cᵢ − C_V`. `Sim.P` and hybrid H5 (pp. 40 to 41)
compute `Z = x₀•U' + Σᵢ γᵢ•Xᵢ − C_V`, without `xᵣ•U'`.

**Gap.** The simulated `π_p` is a proof for a statement the server never
checks.

**Formalized.** `Sim.P` holds neither `xᵣ` nor `m`, but with `U' = u'•G` for
a scalar `u'` it chooses, `u'•Xᵣ = xᵣ•U'` is computable from the public `Xᵣ`.
The simulator computes `Z = x₀•U' + u'•Xᵣ + Σᵢ γᵢ•Xᵢ − C_V`, which equals the
server's `Z` since `γᵢ•Xᵢ = xᵢ•Cᵢ` as well. Errata item 15, recorded on
issue #149.

### 3. `U'` is a nonzero element

**Printed.** `Sim.P` samples `U' ←$ 𝔾` (p. 40), and hybrid H5 calls `U'`
"perfectly indistinguishable from the real one".

**Gap.** The honest `U' = r•U` has `r ←$ ℤ_p×` (§5.1, p. 33, and errata
item 8) and `U ≠ 0`, so it is uniform on the nonzero elements. The two
distributions differ by `1/p`.

**Formalized.** The simulator samples `u' ←$ ℤ_p×`, so `U' = u'•G` is uniform
on the nonzero elements as well. Errata item 14, recorded on issue #149.

### 4. The condition of Remark 5.9 is a hypothesis

**Printed.** Hybrid H3 (p. 41) extracts from a `π_is` that the issuer produced
after receiving the simulated `π_iu` of H1, and the reduction of H2 runs the
simulator of `ZKP_cmz.iu` inside the zero-knowledge game of `ZKP_cmz.p`.
Remark 5.9 (p. 42) says the gap closes with "different random oracles" per
proof system, or for Schnorr proofs because "the vector sizes mismatch", and
gives no proof. The theorem has no hypothesis about it.

**Gap.** The §3.3 games offer the random oracle only, so neither step follows
from the printed advantages alone.

**Formalized.** `μCMZ_anonymity` adds the condition as explicit arguments,
which a user of the theorem must supply.

- `Piu`, `Pis` and `Pp`, three regions of the hash domain, one per proof
  system.
- `hiu`, `his` and `hp`, the setup, the prover and the verifier of each
  system read and write the oracle table inside its region only
  (`ConfinedSystem`).
- `hiuSim` and `hpSim`, the same for the simulators of `ZKP_cmz.iu` and
  `ZKP_cmz.p`.
- `hext`, the same for the extractor of `ZKP_cmz.is`.
- `hiu_is`, `hiu_p` and `his_p`, the three regions are pairwise disjoint.

**Why regions.** They keep the statement faithful to the paper. The paper has
one random oracle `H_p` for every proof system (§3, p. 24), the anonymity
game threads one table through every party, and the Remark's remedy is
"different random oracles" per proof system. Confining each system to its own
region of the one oracle is the same thing. The restriction of a lazy random
oracle to a region is a random oracle on that region, and the restrictions to
disjoint regions are independent. So three systems confined to disjoint
regions behave as three systems with three oracles, while the game, the
parties and the printed advantages keep the single oracle. For the
Fiat–Shamir Σ-protocols the region of a system is the set of transcript hashes
of its statement shape, and the disjointness is the Remark's mismatch of
vector sizes.

**The lemma.** `ksndSimAdv_le_ksndAdv_of_domainSeparated` is the Remark's
assertion for one extraction. Its hypothesis `DomainSeparated` is the part of
the condition that hybrid H3 uses, the simulator of `ZKP_cmz.iu` confined to
`Piu` (`hiuSim`), the setup and the verifier of `ZKP_cmz.is` and its extractor
confined to `Pis` (`his`, `hext`), and `Piu` disjoint from `Pis` (`hiu_is`).
The instance fact for the Fiat–Shamir Σ-protocols belongs to issue #3.

### 5. The crs is fixed in the §3.3 views

**Printed.** Definition 4.4 quantifies over the crs pointwise, while the §3.3
games sample it inside.

**Formalized.** The views `riuNIZKP`, `risNIZKP` and `rpNIZKP` return the `H`
of the statement from setup, so the three advantages of the bound are taken
at the `H` of the anonymity game. `Framework/Anonymity.lean` leaves this
bridge to the theorem.

### 6. `gen ≠ 0` and `H ≠ 0`

**Printed.** `G` is a generator and the crs `H` is sampled from the group
(Figure 9), and the proof uses both tacitly.

**Gap.** With `H = 0` every `x₀` opens `X₀ = 0`, so the extracted `x₀` need
not be the key's and `Sim.P` computes a `Z` that differs from the server's.
With `gen = 0` every public base is `0`, the honest `C'` is always `0` and the
simulated one is uniform.

**Formalized.** Both are hypotheses of the theorem. `H ≠ 0` is the crs of
issue #149.

### 7. The game starts from the empty oracle table

**Printed.** Definition 4.4 runs setup and key generation first, and for μCMZ
both are oracle-free, so the table is empty when the issuer and the user
start, as it is in the §3.3 games.

**Formalized.** The framework's game takes an initial table as a parameter,
and the theorem fixes it to the empty one, which the lifted setup and key
generation leave by `runRO_liftM`.
-/

namespace KVAC.Schemes.MicroCMZ

open OracleComp KVAC.Core KVAC.Framework ENNReal

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [DecidableEq G] [SampleableGroup F G]
variable (HS : HashSpec) (gen : G)

/-! ## The proof systems as §3.3 objects

Per the reading of issue #176, the parameters `πiu n`, `πis` and `πp n` of the
credential are §3.3 proof systems for `R_cmz.iu`, `R_cmz.is` and `R_cmz.p`.
`riuNIZKP`, `risNIZKP` and `rpNIZKP` are those views, with the crs fixed at the
`H` of the statement. Definition 4.4 quantifies over the crs pointwise and the
§3.3 games sample it, and the fixed crs is the bridge between the two
(`docs/DESIGN_ALTERNATIVES.md`). -/

/-- `ZKP_cmz.iu` as a §3.3 proof system at the crs `H` for `R_cmz.iu` (O24 Eq. 9). -/
noncomputable def riuNIZKP {n : ℕ} (H : G) (π : RiuProofSystem HS G F n) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun _ => pure H) (fun _ x w => riuRel gen x w = true)

/-- `ZKP_cmz.is` as a §3.3 proof system at the crs `H` for `R_cmz.is` (O24 Eq. 10). -/
noncomputable def risNIZKP (H : G) (π : RisProofSystem HS G F) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun _ => pure H) (fun H' x w => risRel gen H' x w = true)

/-- `ZKP_cmz.p` as a §3.3 proof system at the crs `H` for `R_cmz.p` (O24 Eq. 11). -/
noncomputable def rpNIZKP {n : ℕ} (H : G) (π : RpProofSystem HS G F n) :
    NIZKPSyntax (OracleComp (ZKRO HS)) :=
  π.toNIZKPSyntax (fun _ => pure H) (fun H' x w => rpRel gen H' x w = true)

/-- The relation of `riuNIZKP` is decidable. -/
abbrev riuDecRel {n : ℕ} (H : G) (π : RiuProofSystem HS G F n) :
    (riuNIZKP HS gen H π).DecidableRelation :=
  fun _ x w => show Decidable (riuRel gen x w = true) from inferInstance

/-- The relation of `risNIZKP` is decidable. -/
abbrev risDecRel (H : G) (π : RisProofSystem HS G F) :
    (risNIZKP HS gen H π).DecidableRelation :=
  fun H' x w => show Decidable (risRel gen H' x w = true) from inferInstance

/-- The relation of `rpNIZKP` is decidable. -/
abbrev rpDecRel {n : ℕ} (H : G) (π : RpProofSystem HS G F n) :
    (rpNIZKP HS gen H π).DecidableRelation :=
  fun H' x w => show Decidable (rpRel gen H' x w = true) from inferInstance

/-! ## The simulators and the extractor

Definition 4.4 asks for an algorithm that plays the user without the attributes
`m`. The proof of Theorem 5.8 (§5.4, p. 40) builds it from three objects that
the proof systems provide. The zero-knowledge simulator of `ZKP_cmz.iu`
produces `π_iu` from the statement `(C', X, φ)` alone. The extractor of
`ZKP_cmz.is` recovers the witness `(x₀, u)` of the issuer's proof `π_is`. The
zero-knowledge simulator of `ZKP_cmz.p` produces `π_p` from the statement
`(U', X, C, Z, φ')` alone.

The extractor is a `TraceExtractor`, a function of the statement, the proof and
the oracle table, departure 1 of the module docstring. -/

/-- The zero-knowledge simulator of `ZKP_cmz.iu` at the crs `H : G`. -/
abbrev RiuSimulator {n : ℕ} (π : RiuProofSystem HS G F n) : Type :=
  G → RiuStmt G F n → StateT HS.Cache ProbComp π.Proof

/-- The zero-knowledge simulator of `ZKP_cmz.p` at the crs `H : G`. -/
abbrev RpSimulator {n : ℕ} (π : RpProofSystem HS G F n) : Type :=
  G → RpStmt G F n → StateT HS.Cache ProbComp π.Proof

/-- The trace extractor of `ZKP_cmz.is` at the crs `H : G`. -/
abbrev RisExtractor (π : RisProofSystem HS G F) : Type :=
  G → RisStmt G → π.Proof → HS.Cache → ProbComp (Option (RisWitness F))

/-- A `RiuSimulator` as the `ZKSimulator` of `riuNIZKP`. -/
def riuSimToZK {n : ℕ} (H : G) (π : RiuProofSystem HS G F n) (s : RiuSimulator HS π) :
    ZKSimulator HS (riuNIZKP HS gen H π) :=
  fun {_} crs x => s crs x

/-- An `RpSimulator` as the `ZKSimulator` of `rpNIZKP`. -/
def rpSimToZK {n : ℕ} (H : G) (π : RpProofSystem HS G F n) (s : RpSimulator HS π) :
    ZKSimulator HS (rpNIZKP HS gen H π) :=
  fun {_} crs x => s crs x

/-- A `RisExtractor` as the `TraceExtractor` of `risNIZKP`. -/
def risExtToTrace (H : G) (π : RisProofSystem HS G F) (e : RisExtractor HS π) :
    TraceExtractor HS (risNIZKP HS gen H π) :=
  fun {_} crs x pr c => e crs x pr c

variable (πiu : ∀ n, RiuProofSystem HS G F n) (πis : RisProofSystem HS G F)
  (πp : ∀ n, RpProofSystem HS G F n)

/-! ## The simulation oracle of Remark 5.9

**Hybrid H3** (p. 41) extracts from a `π_is` that the issuer produced after
receiving the simulated `π_iu` of H1. That is knowledge soundness of
`ZKP_cmz.is` with a simulation oracle for `ZKP_cmz.iu`, the game `ksndSimGame`
of `Core/NIZKP/Composition` with advantage `KSNDSimAdv`, not the printed
`Adv^ksnd`.

**Hybrid H2** runs, in its reduction, the same simulator of `ZKP_cmz.iu`
inside the zero-knowledge game of `ZKP_cmz.p`.

**The hypotheses.** The theorem takes the condition of Remark 5.9 as
hypotheses. Each proof system, its simulator or its extractor, is confined to
its own region of the random-oracle domain, and the regions are pairwise
disjoint.

**The oracle.** `riuSimulationOracle` is the simulator of `ZKP_cmz.iu` as the
simulation oracle with respect to `ZKP_cmz.is`. The lemma
`ksndSimAdv_le_ksndAdv_of_domainSeparated` discharges H3 with it. -/

/-- The simulator of `ZKP_cmz.iu` as the simulation oracle with respect to
`ZKP_cmz.is`, the oracle the issuer holds when it produces `π_is` in hybrid H3. -/
noncomputable def riuSimulationOracle (n : ℕ) (H : G) (simIu : ∀ n, RiuSimulator HS (πiu n)) :
    SimulationOracle HS (risNIZKP HS gen H πis) where
  Query := fun _ => RiuStmt G F n
  spec := fun _ _ => (πiu n).Proof
  impl := fun H' x => simIu n H' x

/-! ## The simulator of Theorem 5.8

`μCMZAnonSimulator` takes the two simulators and the extractor as parameters
and wires them as follows. `AnonSimulator` splits the interactive `Sim.I` of
the paper into its two moves, `simI₁` before the issuer's response and `simI₂`
after it, written `Sim.I₁` and `Sim.I₂` below, and `Sim.P` is `simP`.

`Sim.I₁`. Sample `C' ←$ 𝔾` and send it with a simulated `π_iu`. The
honest commitment `Σᵢ mᵢ•Xᵢ + s•G` has the same distribution, since `s` is
uniform.

`Sim.I₂`. On the issuer's response `(U', V', π_is)`, check `U' ≠ 0`
and verify `π_is` on `(X₀, C' + Xᵣ, U', V')`, as the honest user does, and
reject otherwise. Then extract `(x₀, u)` from `π_is`, check that it satisfies
`R_cmz.is`, and store `x₀`. The scalar `x₀` is the discrete logarithm of `X₀`
in base `H`, the only part of the issuer's key that presentations need. A
failed extraction is a rejection, the abort of hybrid H3.

`Sim.P`. Sample `u' ←$ ℤ_p×`, `C_V ←$ 𝔾` and `γᵢ ←$ ℤ_p`, and set `U' = u'•G`
and `Cᵢ = γᵢ•G`. The honest `r•U`, `V' + r'•H` and `mᵢ•U' + rᵢ•G` have the same
distributions. Compute `Z = x₀•U' + u'•Xᵣ + Σᵢ γᵢ•Xᵢ − C_V`, which equals the
server's `Z = (x₀ + xᵣ)•U' + Σᵢ xᵢ•Cᵢ − C_V`, since `u'•Xᵣ = xᵣ•U'` and
`γᵢ•Xᵢ = xᵢ•Cᵢ`. Send `(U', C_V, C)` with a simulated `π_p` for that `Z`.

The term `u'•Xᵣ` and the nonzero `U'` are departures 2 and 3 of the module
docstring.

The state is one type for `Sim.I₁`, `Sim.I₂` and `Sim.P`, as
`AnonSimulator` requires. It holds the public parameters, `C'` and `x₀`, with
`0` in place of `x₀` before extraction. -/

/-- The simulator state `st_Sim`, the public parameters, the commitment `C'` and
the extracted `x₀`, `0` before extraction. -/
abbrev μCMZSimState (n : ℕ) : Type := Params G n × G × F

/-- The simulator `Sim = (Sim.I, Sim.P)` of O24 Theorem 5.8 (§5.4, p. 40), over
the simulators of `ZKP_cmz.iu` and `ZKP_cmz.p` and an extractor of
`ZKP_cmz.is`. `Sim.I` is the two moves `simI₁` and `simI₂`, before and after
the issuer's response, and `Sim.P` is `simP`. -/
noncomputable def μCMZAnonSimulator (simIu : ∀ n, RiuSimulator HS (πiu n))
    (simP : ∀ n, RpSimulator HS (πp n)) (extIs : RisExtractor HS πis) :
    AnonSimulator HS (μCMZCredentialSyntax F HS gen πiu πis πp) where
  SimState := fun {_ n} _ => μCMZSimState (F := F) (G := G) n
  -- Sim.I₁. A random C' and a simulated π_iu for (C', X, φ).
  simI₁ := fun {_ n} H pp φ => do
    let C' ← liftM ($ᵗ G)
    let π ← simIu n H (C', pp.2.2, φ)
    pure ((pp, C', (0 : F)), (C', π))
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

/-! ## Theorem 5.8

The bound is the printed one, with `Adv^ksnd` as printed. The hypotheses are
departures 4 to 7 of the module docstring. Errata item 16 records the
subscript `ZKP_cmz.iu` printed in the bound of H2, which simulates `π_p`.
Errata item 17 records the `Adv^simex` of Theorem 1 (§1, p. 4) against the
`Adv^ksnd` of Theorem 5.8. -/

/-- **O24 Theorem 5.8.** For `gen ≠ 0`, `H ≠ 0`, `(sk, pp) ∈ [K(H)]` and
`φ(m) = 1`, the anonymity advantage of μCMZ from the empty random-oracle table
with respect to `μCMZAnonSimulator` is at most the zero-knowledge advantages of
`ZKP_cmz.iu` and `ZKP_cmz.p` plus the knowledge-soundness advantage of
`ZKP_cmz.is`, for reductions `A'`, `D'` and `A''`. The hypotheses `hiu` to
`hpSim` are the condition of Remark 5.9. The proof is deferred. -/
theorem μCMZ_anonymity (simIu : ∀ n, RiuSimulator HS (πiu n))
    (simP : ∀ n, RpSimulator HS (πp n)) (extIs : RisExtractor HS πis)
    (hgen : gen ≠ 0) {secParam n : ℕ} (H : G) (hH : H ≠ 0) (sk : Key F n)
    (pp : Params G n) (hkeys : (sk, pp) ∈ support (keygen (F := F) (n := n) H gen))
    (m : Fin n → F) (φ : Policy F n) (hφ : φ m = true)
    (issuer : AnonIssuer HS (μCMZCredentialSyntax F HS gen πiu πis πp))
    (D : AnonDistinguisher HS (μCMZCredentialSyntax F HS gen πiu πis πp) issuer.StA)
    (Piu Pis Pp : Region HS)
    (hiu : ConfinedSystem HS (riuNIZKP HS gen H (πiu n)) Piu)
    (hiuSim : ZKSimulatorConfinedTo (riuSimToZK HS gen H (πiu n) (simIu n)) Piu)
    (his : ConfinedSystem HS (risNIZKP HS gen H πis) Pis)
    (hext : TraceExtractor.ConfinedTo (risExtToTrace HS gen H πis extIs) Pis)
    (hp : ConfinedSystem HS (rpNIZKP HS gen H (πp n)) Pp)
    (hpSim : ZKSimulatorConfinedTo (rpSimToZK HS gen H (πp n) (simP n)) Pp)
    (hiu_is : Piu.Disjoint Pis) (hiu_p : Piu.Disjoint Pp) (his_p : Pis.Disjoint Pp) :
    ∃ (A' : ZKAdversary HS (riuNIZKP HS gen H (πiu n)))
      (D' : ZKAdversary HS (rpNIZKP HS gen H (πp n)))
      (A'' : KSNDAdversary HS (risNIZKP HS gen H πis)),
      AnonAdv HS (μCMZCredentialSyntax F HS gen πiu πis πp) issuer D
          (μCMZAnonSimulator HS gen πiu πis πp simIu simP extIs)
          (secParam := secParam) (n := n) H sk pp m φ ∅ ≤
        ZKAdv HS (riuNIZKP HS gen H (πiu n)) (riuDecRel HS gen H (πiu n)) A'
            (riuSimToZK HS gen H (πiu n) (simIu n)) secParam
        + ZKAdv HS (rpNIZKP HS gen H (πp n)) (rpDecRel HS gen H (πp n)) D'
            (rpSimToZK HS gen H (πp n) (simP n)) secParam
        + (KSNDAdv HS (risNIZKP HS gen H πis)
            (TraceExtractor.toKSND (risExtToTrace HS gen H πis extIs)) A''
            (risDecRel HS gen H πis) secParam).toReal := by
  sorry

end KVAC.Schemes.MicroCMZ
