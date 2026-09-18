# μCMZ, remaining work on the path to Theorem 1

Sixteen statements and one group of open issues. Arrows point from a prerequisite to the statement that needs it. Numbers are the items of `docs/MICROCMZ_REMAINING.md` at 73c8d3d. Items 4, 7, 11 and 15 are absent, since they are deferrable, a decision, or corollaries off the path to Theorem 1. The sub-lemma PRs, merged or open, are absent. The nine open issues of Lemma 5.4 stand for the remaining sub-lemmas as one group.

```mermaid
graph BT
  T1["20 · Theorem 1"]
  T52["16 · Theorem 5.2"]
  T53["19 · Theorem 5.3"]
  T51["8 · Theorem 5.1"]
  L54["5 · Lemma 5.4 proof (sorry)"]
  SUB["Open issues 108 to 116, Lemma 5.4 sub-lemmas"]
  L55["6 · Lemma 5.5, Claims 5.6 and 5.7, general n"]
  D44["9 · Definition 4.4, anonymity game"]
  T58["10 · Theorem 5.8, simulators and bound"]
  E12["12 · extractablePoly_obligation, statement correction (sorry), proved by 13"]
  N14["14 · newUsr_mac_isSome, cache transport lemma (sorry)"]
  T510["13 · Theorem 5.10, eight steps"]
  V18["18 · μCMZ_AT keeping π_is"]
  T511["17 · Theorem 5.11, Claims 5.12 to 5.14, lifting lemma"]
  K1["1 · KVACSyntax instance and CorrectRO"]
  P2["2 · Predicate family and Enforces proofs"]
  H3["3 · ZKP proves R ⊇ R_cmz, composition clause"]

  T52 --> T1
  T53 --> T1
  K1 --> T52
  T58 --> T52
  T510 --> T52
  D44 --> T58
  H3 --> T58
  P2 --> T58
  K1 --> T58
  E12 --> T510
  N14 --> T510
  T51 --> T510
  H3 --> T510
  K1 --> N14
  L54 --> T51
  L55 --> T51
  SUB --> L54
  L54 --> L55
  V18 --> T53
  T58 --> T53
  T511 --> T53
  K1 --> V18
  V18 --> T511
  H3 --> T511

  classDef root fill:#4a5a8a,color:#fff,stroke:#4a5a8a
  classDef thm fill:#dfe4f3,color:#1f1f1f,stroke:#4a5a8a
  classDef sorry fill:#f6e3c5,color:#1f1f1f,stroke:#b7791f
  classDef leaf fill:#e3efe3,color:#1f1f1f,stroke:#3c7a3c
  class T1 root
  class T52,T53,T51,T58,T510,T511,L55,V18 thm
  class L54,E12,N14 sorry
  class SUB,K1,P2,H3,D44 leaf
```

| Colour | Meaning |
| --- | --- |
| dark blue | root |
| light blue | to state and prove |
| orange | stated, proof or statement correction pending |
| green | leaf, can start now |

## Depth from the leaves

A node's level is one more than the maximum level of its prerequisites. Leaves sit at level 0.

| Level | Items | Prerequisites |
| --- | --- | --- |
| 0 | 1, 2, 3, 9, 12, open issues 108 to 116 | none in the list |
| 1 | 5, 10, 14, 18 | the issues for 5. Items 1, 2, 3, 9 for 10. Item 1 for 14 and 18 |
| 2 | 6, 17 | 5 for 6. 3 and 18 for 17 |
| 3 | 8, 19 | 5, 6 for 8. 10, 17, 18 for 19 |
| 4 | 13 | 1, 3, 8, 12, 14 |
| 5 | 16 | 1, 10, 13 |
| 6 | 20 | 16, 19 |

## Decisions that fix statements in the graph

The decisions paragraph of `docs/MICROCMZ_REMAINING.md` names nine open decisions. Eight touch nodes shown here. The ninth, the rescope of #3, touches only the excluded item 4.

| Decision | Items |
| --- | --- |
| AGM game or plain MAC game as the target (item 7) | 8, 17 |
| Knowledge soundness or simulation extractability (Remark 5.9) | 3, 10, 13 |
| Printed Theorem 5.3 and Theorem 1 bounds, or the proof-derived shapes only | 19, 20 |
| Concrete inequalities at fixed F and G, or asymptotic negligibility over a λ-indexed family (#148) | 12, 16 |
| How `CorrectRO` reaches game states, the cache extension bridge of #118 | 1, 14 |
| Composition clause of the ZKP hypothesis | 3 |
| Extractor interface and Z recovery | 13 |
| Query factors or a multi-instance notion | 13 |

The arrows establish the conjunctions. The printed quantitative bounds of Theorem 5.3 and Theorem 1 follow only once the third decision is taken, since item 20 records that the printed Theorem 1 bound is not the sum of the Theorem 5.2 and 5.3 bounds.

Built from `docs/MICROCMZ_REMAINING.md` at 73c8d3d and the issue states on 11 September 2026.
