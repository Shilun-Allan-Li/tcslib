# The configuration facts (PR #190, an API gate): resolutions

**Staged (2026-11-04):** `pack.md`, at #190's head `3cc6c9ee`. Bundle `94-cfg-facts-api-bundle.md`, SHA-256
`e90a023256445ce9060bed8bd19476aacd9bfe74572217c6822b6210cc36ff09` (66 sections), the records at `df348829`; in the exchange
`arora-barak-ch3-4/outbox/gates/94-cfg-facts-api-gate/`.
**Dispatched (user, 2026-11-04);** the folder archived.

**Round 1** (`pack.md`, head `3cc6c9ee`). **Findings** (`findings.md`, verbatim, SHA-256
`2c8c6337d862033b0e532aff2f897d2a178aa9a5502558b41e418690dcb1baf3`; received 2026-11-05): **CLOSE, 0 blockers,
0 majors, 2 minors, 7 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The NF screen account conflates the pending delivery with the PR tree; the F2 list has 19 names, not 15, and two are re-pointed. | **True; corrected** in the ledger (RN-1): the current residual by file. NF's own copies are checked at its landing (#191). |
| 2 | minor | RN-1 lacks per-file accounting; 21 members in `ZoneRebalance`, and `phaseHostTM_run` and `xr_E_initCfg`. | **True; corrected** in the ledger: the members by file, none above one fifth. |
| 3–8 | note | Integrity; statements; `length_flatMap_uniform`; the re-points; rule 10; screen, names, lint. | Agreed. On note 5, the membership-local hypothesis is a possible later generalization; the current form matches its consumers. |
| 9 | note | The final merged tree is not yet certified. | Agreed: `replay-lcf3` (86 modules from `oleans-led4`, at `a5d448e3`) is the certifying replay. |

**Gate 94 closes (round 1, CLOSE, 2026-11-05).** #190 is clear to merge once `replay-lcf3` passes.
