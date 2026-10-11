# 12.2c T1 batch 11A gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 1 minor, 9 notes

Findings verbatim in `audits/12.2c-t1-loop-findings.md`. Pack:
`audits/12.2c-t1-loop-pack.md`. The auditor applied the patch to the attached
base, reproduced both after files exactly, and reran the screen and the Loop
census byte for byte: 673 → 540 pairs, Loop census 98/198 → 92/193.

| Finding | Disposition |
|---|---|
| 1 (minor): `loopHost_contracts`'s historical docstring names the deleted `loopHost_body_capture` | **Swept** on the PR branch by a separately authorized documentation edit (the brief had frozen this docstring). The sentence now reads "`loopHost_body_run` (historically `loopHost_body_capture`)". The change is comment-stripped identical, and Loop re-checks at 0 errors and 0 sorries. No wrapper was restored |
| 2–3, 5–7, 9 (notes) | Freeze, the three run facts, the host tables (including RB5's `t = 0` anchor case), the scan abstraction, the screen and census reproduction, and the logs all confirmed. No action |
| 4 (note): the three additions plus the existing `output_prefix` and `runFrom_of_halt` cover all five of `EmitIterEmbed`'s run facts | **Carried** to 12.2c T2 (item 6, CH7-D2's EmitIter half), with the probe's P2 call shapes |
| 8 (note): no unacknowledged debt. E1 is the accepted relocation; `loopHost_fuel_copy` stays disclosed (Catalog shares down from 93/89% to 90/86%) | **Carried**: in T3, Catalog's `f2_loop_live_prefix` becomes a citation of `runFrom_state_ne_none_of_le`; the remaining Loop clusters go to 11B |
| 10 (note): the census's other inputs (`Primitives`, `Composition`, `TimeConstructible`, `Wrappers`), the base replay log, and the zip were not attached | **Pack practice:** attach every input a cited generator reads, plus the base replay log, and state the evidence boundary explicitly |

**Gate CLOSED. PR #20 is clear to merge.**
