# MIG-12 continuation 1: `Build/CfgRecord` onto the contract layer (PR #150, a fill gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the fill gate of PR #150 (`lean/mig12-cfgrecord-cont1` at `79de6551`: the delivery's six
commits and the maintainer's `79de6551`, on the campaign branch at `e9b48616`). Pack `pack.md`;
bundle SHA-256 `e4e968cd6267adc6b993f22b0b2adce4ff036468abc5b39fd2022d7da47fd28b` (151 sections;
folder `64-mig12-cfgrecord-cont1-fill-gate/`), built from the Lean files at `79de6551` and the
records at `d6b2ed92`. By the user's ruling (2026-10-23) it was dispatched before the post-#149
replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-23, SHA-256
`c25814875a86390e6f5d8ece205d6a242d5d48798dfa6fb6cf5b7a92bc9a973b`): **PASS, 0 blockers, 0 majors,
2 minors, 10 notes. The gate is closed.** The maintainer checked both minors directly: both true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `exists_recordStepTM`'s frozen sketch opens "Compose by R2 seams", but the machine is one `phaseHostTM` whose phases concatenate through `Segment.trans` (the docstring's later appendix says so); a pre-existing inconsistency. | **True** (line 4661 at `79de6551`). **Ruled (user, 2026-10-23): fix it in #150.** Commit `8d9e3b5e`, docstring only: the sketch's first sentence now says the reads compose inside one phase host (`phaseHostTM`), the phases' segments joined by `Turing.Segment.trans`. The code is identical with comments stripped, the statement is unchanged, and the module elaborates against `oleans-lsk2` with no output (`evidence/round1-fix/`). A docstring-only change needs no gate. |
| 2 | minor | Counts: 22 framed run calls (20 `_run_ofCfg`, 2 `_run_succ_ofCfg`), not 23; the landed increase is 5,717 − 5,310 = 407 (402 is the delivered file's), and 415 from the original base. | **True; errata.** At the patched base the literal `_run_ofCfg` count is 23, of which 3 are in docstrings; the code has 20 `_run_ofCfg` and 2 `_run_succ_ofCfg` calls, all gone at the head. Sizes: the original base 5,302 lines, the patched base 5,310, the delivered file 5,712 (+402), the landed file 5,717 (+407 from the patched base, +415 from the original base). #150's description is corrected; the review, the report and the dispatched pack stay as they are. |
| 9 | note | The duplication increase is disclosed and within the accepted route. | **Agreed.** The generic-reader compression item (MIG-12-C) stays scheduled; the swap is not described as having achieved the estimated reduction. |
| 11 | note | F5's ten report discrepancies are records gaps, not correctness gaps; the report's phase-1 compression claim is wrong. | **Agreed;** the review's corrections stand beside the report. |
| 12 | note | The pending replay is a separate merge prerequisite; the `git merge-tree` result is not saved. | **Agreed.** After #149 merges, the campaign branch is merged into #150 (its merge is recorded), and the 52-module closure replays from #149's merged-tree snapshot, with the head, the snapshot and the admission set recorded. |
| 3–8, 10 | notes | Integrity; the public freeze and the authorized documentation; the swap's fidelity; the scalar conversion; rule 10 and rule 11; boundary cases; the elaboration, axiom, probe and lint records. | No action. |

**Merge state. #150: not yet clear to merge.** Its replay runs after #149 merges.
