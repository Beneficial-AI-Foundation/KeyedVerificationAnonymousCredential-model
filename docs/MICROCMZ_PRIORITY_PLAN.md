# μCMZ priority delivery plan

> **Status:** This plan supersedes [`PLAN.md`](PLAN.md) and [`TRACKS.md`](TRACKS.md) for the duration of the Signal-driven μCMZ delivery phase (now → ~2026-08-01). Once the production swap lands, the full two-scheme plan in `PLAN.md` resumes.
>
> Authored by Christiano Braga; polished and consolidated by the project team. Significant revisions discussed on the [Signal Shot Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/583276-Signal-Shot) before landing here.

A μCMZ-only roadmap toward the Signal milestones, derived from [`PLAN.md`](PLAN.md) and [`TRACKS.md`](TRACKS.md). The canonical two-scheme plan remains the long-term reference; this document narrows scope to μCMZ and prioritises a credible public deliverable on a deadline.

The reference paper, cited as **O24**, is Michele Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, [IACR ePrint 2024/1552](https://eprint.iacr.org/2024/1552). The formal simulation-extractability definition O24 defers to is **DG23** (Dao–Grubbs, ePrint 2023/494).

## Driver

Rolfe (Signal), goal as stated:

> "Our current goal is to have the base proof and credential system public by the end of June and to start replacing production credentials by August."

Dates (today = **2026-06-03**):

- **2026-06-18** — 15-day internal target: bare-minimum μCMZ spec + statements.
- **2026-06-30** — public: construction + correctness *proved*, all μCMZ security results *stated* and type-checking.
- **~2026-08-01** — production swap: the AGM reductions filled in.

## Reframing for μCMZ

Three decisions distinguish this plan from the canonical two-scheme plan.

### 1. The proof system is a hypothesis, not something we build

O24's μCMZ theorems are conditional on the ZKP's properties (Theorem 5.8 "given a knowledge-sound ZKP"; Theorem 5.2 "if ZKP is a proof system for `R ⊇ R_cmz`" and "assume the proof itself can provide a candidate instance"). So **Track Σ (Σ-protocol meta-theory, Fiat–Shamir, straight-line extraction, Sec. 9) leaves the critical path**. We take those as properties of the abstract NIZK (`Core/NIZKP/Basic.lean`), exactly as O24 does. This removes the single largest infrastructure block.

### 2. Two registers

The model-agnostic NIZK layer (Layer 0 of `Core/NIZKP/Basic.lean`) gives the proof-system *syntax* and symbolic properties for free. μCMZ's quantitative theorems (`Adv ≤ 2·Adv^3dl + … + Adv^zk`) are **game-based**, stated in VCV-io `OracleComp` style. The two registers meet at the NIZK *syntax* plus a *computational* `SecurityModel` instance. The μCMZ security theorems live in the game register and consume the NIZK as the proof-system component.

### 3. Relax Framework generality

`PLAN.md` requires `Framework/` be driven by Definitions 4.2–4.5 of O24 so μBBS also fits. With μBBS deferred, that constraint is pure cost; we state μCMZ's correctness / anonymity / extractability more directly, accepting a future refactor if μBBS returns. **This diverges from the canonical plan** — flagged on Zulip; the refactor cost is judged acceptable.

## Estimation baseline

Estimates are calibrated against the NIZK module (issue **#20**, `Core/NIZKP/Basic.lean`, PR #26): started 2026-05-27, PR-ready 2026-06-03 (~7 calendar days, interleaved). That deliverable is one heavily-documented abstract spec module with security properties **stated, not proved**, plus novel carrier design.

- **1 NIZKP-unit ≈ 20 AI-supported hours** (interactive human + AI session time, not wall-clock; ≈ 3 focused days).
- Spec/definition modules are now **cheaper** per unit — the architecture exists.
- Proof modules are **dearer** — NIZK only stated properties; AGM reductions are heavier than anything attempted so far.
- Uncertainty ±40% on definitions/statements, ±60% on the AGM proof.

## Itemized work, organised by dependency

Tier 0 is done. Each later tier depends on the ones above it.

### Tier 0 — foundation (done)

| # | Item | Issue | Status |
|---|---|---|---|
| 0a | `Core/Group` | #18 | done (PR #22) |
| 0b | `Core/AlgebraicMAC` | #21 | done (PR #24) |
| 0c | `Core/NIZKP/Basic` | #20 | done (PR #26) — 1 unit spent |

### Tier 1 — foundation additions

| # | Item | Depends | Issue | Units | Hours |
|---|---|---|---|---|---|
| 1 | NIZK `StrongSimExtractable` (candidate-statement extractor) | 0c | #20 (follow-up) | 0.15 | 3 |
| 2 | `Preliminaries/Assumptions`: **3-DL** statement (bind VCV-io DL) | 0a | #2 | 0.2 | 4 |

### Tier 2 — minimal Framework (μCMZ-direct)

| # | Item | Depends | Issue | Units | Hours |
|---|---|---|---|---|---|
| 3 | `Framework/Syntax` (Def 4.2, `(S, K, I, P)`) | 0a, 0c | #4 | 0.4 | 8 |
| 4 | `Framework/Correctness` definition (Def 4.3) | 3 | #4 | 0.2 | 4 |
| 5 | `Framework/Anonymity` game (Def 4.4, VCV-io `OracleComp`) | 3, 0c | #5 | 0.6 | 12 |
| 6 | `Framework/Extractability` game (Def 4.5, multi-user MITM) | 3, 1 | #5 | 0.7 | 14 |

### Tier 3 — μCMZ spec ("the credential system")

| # | Item | Depends | Issue | Units | Hours |
|---|---|---|---|---|---|
| 7 | `MicroCMZ/Construction` (§5.1: KeyGen / Setup / Issue(φ) / Present) | 3, 0a, 0c | #6 | 0.7 | 14 |
| 8 | μCMZ **correctness PROOF** (presentation identity, algebra) | 7, 4 | #6 | 0.5 | 10 |
| 9 | `MicroCMZ/AlgebraicMAC` instance + **Theorem 5.1 statement** | 7, 0b, 2 | #8 | 0.4 | 8 |

### Tier 4 — μCMZ security statements (bodies `sorry`)

| # | Item | Depends | Issue | Units | Hours |
|---|---|---|---|---|---|
| 10 | μCMZ **anonymity statement** (Theorem 5.8) | 5, 7 | #10 | 0.25 | 5 |
| 11 | μCMZ **extractability statement** (Theorem 5.2) | 6, 7, 1 | #11 | 0.25 | 5 |

### Tier 5 — μCMZ proofs (post-June → August)

| # | Item | Depends | Issue | Units | Hours |
|---|---|---|---|---|---|
| 12 | μCMZ **anonymity proof** (hybrid; no AGM / 3-DL) | 10 | #10 | 1.0 | 20 |
| 13 | μCMZ **algebraic-MAC UF-CMVA in AGM / 3-DL** (Lemmas 5.4 / 5.5 → Theorem 5.1) | 9 | #8 | 3.5 | 70 |
| 14 | μCMZ **extractability proof** (Theorem 5.2, reduces to 13) | 11, 13 | #11 | 1.5 | 30 |

### Deferred (not μCMZ-minimum)

| Item | Issue |
|---|---|
| Track Σ — Σ-protocol / Fiat–Shamir / straight-line extraction (assumed via NIZK fields) | #3 |
| `Core/Hash` concretization (absorbed into NIZKP; resurfaces with Sec. 8 extensions) | #19 |
| μCMZ one-more unforgeability (Theorem 5.3) | #12 |
| μBBS — all of Sec. 6 | #7, #13, #14, #15, #16 |
| Track Ex — Ristretto instance + concrete run + Lake dependency | #17 |

## Rollups

- **Spec + correctness + all statements** (items 1–11): **≈ 87 h.** Over 15 days ≈ 5.8 h/day solo — overshoots a realistic window.
- **15-day bare minimum** (items 1, 2, 3, 4, 7, 8, 9, 10 — *defer the extractability game and statement* #6 and #11): **≈ 56 h ≈ 3.7 h/day.** Delivers: construction, correctness *proved*, anonymity *stated*, Theorem 5.1 *stated*. Extractability slips to early July.
- **Anonymity proof** (item 12, +20 h): the one security *proof* reachable shortly after — no AGM required.
- **AGM core** (items 13–14, ≈ 100 h): the July → August work; the machine-checked guarantee before the production swap.

**Totals:** ≈ **56 h** for the end-of-June public deliverable; ≈ **187 h** for a fully-proved μCMZ.

## Milestones

| Date | Deliverable | Items | Proof state |
|---|---|---|---|
| **2026-06-18** | μCMZ spec + base statements | 1, 2, 3, 4, 7, 8, 9, 10 | construction + correctness proved; Theorems 5.1 / 5.8 stated |
| **2026-06-30** | Public release | + 5, 6, 11 | all μCMZ security results stated; type-checks green |
| **early July** | Anonymity proved | + 12 | Theorem 5.8 proved (no AGM) |
| **→ 2026-08-01** | Production-ready | + 13, 14 | Theorems 5.1 / 5.2 proved in AGM under 3-DL |

## What's deferred vs `PLAN.md`

- **μBBS (all of Sec. 6)** — Tracks BBS-C, BBS-M, BBS-A, BBS-E, BBS-OMUF (#7, #13, #14, #15, #16). Resumes after the production swap.
- **Track Σ — Σ-protocol meta-theory, Fiat–Shamir, straight-line extraction** (#3). Replaced for the priority phase by abstract NIZK fields on `Core/NIZKP/Basic.lean`; per O24's own framing of μCMZ's theorems as conditional on a knowledge-sound ZKP.
- **`Core/Hash.lean`** (#19). The paper's `Hp` random oracle lives inside the Fiat–Shamir construction of the NIZK; if we treat the NIZK abstractly, `Hp` is encapsulated. `HG` (hash-to-curve) is only used by Sec. 8 extensions (pseudonyms, PRFs), which are out of v1 scope. Resurfaces if Track Σ or Sec. 8 returns to scope.
- **Track Ex — Ristretto instance + concrete run + dalek Lake dependency** (#17). Not required to land before the production swap; the August deliverable can ship against the abstract `PrimeOrderGroup` typeclass.
- **μCMZ one-more unforgeability** (Theorem 5.3, #12). The anonymous-token variant. Not on Signal's critical path.

## Framing for Signal

End-of-June public = the credential system runs and type-checks, correctness is *proved*, and every μCMZ security result is *stated* faithfully against O24 with reductions left as `sorry`. This matches O24's own conditional structure and `PLAN.md`'s "prove or state-with-`sorry`" v1 doctrine. The AGM reductions land between July and the August production cutover, when the guarantee becomes fully machine-checked.

## Return path to `PLAN.md`

Once the August production swap lands, the full two-scheme plan resumes. The expected refactor cost from this phase:

- **Framework relaxation.** `Framework/Anonymity` and `Framework/Extractability` may have absorbed μCMZ-specific shapes that don't fit μBBS as-is. Expected rework: split each into a paper-faithful `Framework/*.lean` (Def 4.4 / 4.5) and a μCMZ-specific specialisation.
- **Track Σ.** Σ-protocol meta-theory, Fiat–Shamir, straight-line extraction become deliverables again, supporting the μBBS extractability proof in particular.
- **Hash.lean.** Resurfaces only if Sec. 8 extensions enter scope, or if a concrete (non-abstract) NIZK is built.
- **μBBS scheme tracks.** Pick up Track BBS-C and the four security tracks under Wave 3 of `PLAN.md`.
