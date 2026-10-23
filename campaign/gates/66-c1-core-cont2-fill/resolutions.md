# C1, R continuation 2: the interpreter core (PR #151, a fill gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the fill gate of PR #151 (`lean/c1-core-cont2` at `f48ea176`: 16 delivery commits, the
maintainer's rule-10 repair `5825c7b6` and docstring commit `f48ea176`, on the campaign branch at
`86523ba5`), with the leaf re-point `89bf6acb` prepared for landing. Pack `pack.md`; bundle SHA-256
`ed339a67aa9d66508c76e71ea5a9e5c55b789569a16294339eaee3ab16c93837` (210 sections; folder
`66-c1-core-cont2-fill-gate/`), built from the Lean files at `f48ea176` and the records at
`d6b2ed92`. By the user's ruling (2026-10-23) it was dispatched before the post-#149 replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-23, SHA-256
`5860b6d13911504c516c1449cffe8688bce84ccfa250cf23df55ddc9f86e3356`): **PASS, 0 blockers, 0 majors,
2 minors, 14 notes. The gate is closed.** The maintainer checked both minors against the cited
records: both true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The report's "eleven startup seams plus the loop seam" overcounts by one: twelve phases have eleven joins (ten in `TPRE`, then the final one), and the proof has eleven `ic_seam_step` applications. | **True; report erratum** (here; the report stays as written): read "ten startup seams plus the final loop seam, eleven altogether". No Lean change: the time ledger is correct. |
| 2 | minor | The review misclassifies the evidence-bearing commits: 15 source-only, one mixed (`d1a49114`, three `.lean` probes, no nested bundle) and three evidence-only, 19 in all; the nested bundle is in `fefcaefa` and `189e4675`. | **True; review erratum** (here; the review stays as written). The review's integrity row 3 and F5 read as above. The landing's restriction to the owned file (16 source-bearing patches by `git am -3 --include`) and the exclusion of the three evidence-only commits are unchanged and correct. |
| 10 | note | The prepared re-point `89bf6acb` is exact. | **Agreed.** It is applied at landing once #153 has merged (the user's ruling). |
| 12 | note | The 85% overlap with `Cfg.mapState_mapState` is a field-equation idiom. | **Agreed;** the user accepted it as an idiom pair (2026-10-23). IR-1's retirement for this file is recorded when the re-point lands. |
| 16 | note | The fill gate is not merge readiness; the replay must pass on the combined tree, including #153 and the re-point where they are part of the landing. | **Agreed.** After #149 (and #153) merge, the campaign branch is merged into #151, the re-point is applied, and the closure replays from the latest merged-tree snapshot. |
| 3–9, 11, 13–15 | notes | Integrity and freeze; faithfulness; the private glue; the time ledger; boundary cases; the admission boundary; rule 10; the re-point's evidence; probes, rule 11 and lint; the corrected records; the public-facing text. | No action. |

**Merge state. #151: not yet clear to merge.** Its replay runs after #149 merges, with the
re-point once #153 is in.
