# Gate 20 · round 2 · CLOSED

The round-2 verdict is **CLEAR**, with 0 blockers, 0 majors, 0 minors and 0 notes.
- **Findings:** `findings-r2/gate20-dl-consolidation-r2-findings.md` (SHA-256
  `95c0f4de9f18c146379156fcf48e3a314f9d9ebf7a347758fd6af1935d422364`). Codex mentions a companion ZIP, but it was not
  received. It is not needed, because the Markdown carries the verdict and the counts.
- **Audited head:** `c2839c41ca6b3a9c34db1595a1ad287768316630`, tree `5eb486b8c2f1901e3c4db08b610840a12d13fe0f`.
- **Pins:** records `1ca834544fa2c866b5e370f97ecd338cad9f1b12`, exchange `ed63370ed1a9edaa412871a5529aa188928bc366`.

| # | Round 1 | Round 2 |
|---|---|---|
| G20-01 | major: raw evidence omitted from the ZIPs | **Closed.** The ZIPs and supplements cover 2441/2441 and 188/188 manifest entries. The raw runs support the census, the seal table (A 33/40 → 34/41, B 28/40 → 30/41, 0 new failing declarations), the 22/22 nm-sim seals and the controls. |
| G20-02 | minor: two missed folds | **Closed.** LE-gate20: the statement is unchanged, the proof uses only published lemmas, and decls2 shows 0 rows. |

**What Codex checked independently**
- **Seals:** it reconstructed 198 seal-probe sources, checked the coverage and the install/EOF counts, and recomputed
  the seal table.
- **Controls:** all 50 paired-control probes give their expected outcomes. That is 90 consolidation, 38 nm-sim and
  10 LE-gate20 sealed negatives, each failing exactly once.
- **Final-landing coverage:** it judged the carry-forward argument sound.
- **Statements:** decls2 reproduces 68/42/2/0.
- **Builds and axioms:** all 114 rebuild records and 1198/1198 final-tree records are clean, and all 33 axiom prints
  are standard.

**PR:** [#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298) was marked ready at `c2839c41`.
- GitHub reports `mergeable_state` clean.
- Base commits after `2ea4df08` change records only.
