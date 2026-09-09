# μCMZ, what remains to state

Branch `microcmz-remaining-statements`, worktree `KVAC-prj/kvac-statements`, from `main` at c5d44ca (9 September 2026). Everything on `main` outside this list is stated and proven.

**Shared prerequisites**
1. μCMZ `KVACSyntax` instance, `Credential.lean` (#163), over abstract `NIZKPSyntax` parameters for R_iu, R_is, R_p, with its correctness `CorrectRO` (Definition 4.3) under completeness of the three parameters.
2. Partial‑disclosure predicate family {φ_a⃗} (#104).
3. Hypothesis "ZKP proves R ⊇ R_cmz" with a composition clause for the shared `ZKRO H` (PR #139 stub).
4. Fiat–Shamir transform of the three Σ‑protocols (#3). Deferrable, the instance is stated over abstract parameters.

**Theorem 5.1, UF‑CMVA (Track CMZ‑M)**
5. Proof of `agm_ufcmva_le_n1_explicit` (Lemma 5.4, stated, `sorry`). Sub‑lemma skeleton in PRs #156 to #158, #161 and #162.
6. Lemma 5.5, the n to 1 reduction, and the general‑n bound `agm_ufcmva_le` (#80).
7. Bridge from the AGM game with Help to plain `UF_CMVAGame`, or the decision to keep the AGM game as the target (#81).

**Theorem 5.8, anonymity (Track CMZ‑A)**
8. Anonymity game, Definition 4.4, `Framework/Anonymity.lean`.
9. Issuance and presentation simulators of §5.4, and the Theorem 5.8 bound (PR #139 states it with `sorry`).

**Theorem 5.10, extractability (Track CMZ‑E)**
10. Steps 1 to 8 of the plan. Extractors and candidate‑Z recovery, Help check, identity lemma, reduction `extToUF`, `NoMultiUser` restriction and partition, four event bounds with the q_I and q_P + 1 factors, the Theorem 5.10 inequality, and the multi‑user extension lemma.
11. `newUsr_mac_isSome` (PR #140, open).

**Theorem 5.2**
12. Conjunction of 8 to 11 at blueprint node `mucmz_extractable_kvac`.

**Theorem 5.3 and 5.11, anonymous token (Track CMZ‑OMUF)**
13. OMUF game, Figure 6 (PR #143, in review). Keygen support lemma and punctured sampler (PR #146). μCMZ_AT core scheme (PR #147).
14. AGM‑instrumented OMUF game, Claims 5.12 to 5.14, the Theorem 5.11 bound, and the π_is lifting lemma.
15. Theorem 5.3 as the conjunction of the 5.8 simulator on the token variant and Theorem 5.11.

**Decisions blocking statements.** Extractor interface and Z recovery (10). Composition clause (3). AGM versus plain MAC game (7). Knowledge soundness or simulation extractability (Remark 5.9). Query factors or multi‑instance notion (10).
