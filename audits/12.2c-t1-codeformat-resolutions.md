# 12.2c T1 item 8 (CH34-D2) gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 0 minors, 16 notes

Findings verbatim in `audits/12.2c-t1-codeformat-findings.md`. Pack:
`audits/12.2c-t1-codeformat-pack.md`. The auditor applied both patches,
reproduced every after-source byte for byte, compared all 79 base public
statements over the six-file union (notes 1, 12), restated `Turing.CodeFormat`
and every new public declaration (notes 2–10), and reran the screen exactly:
117 / 29,824 → 77 / 12,563 (note 13).

| Finding | Disposition |
|---|---|
| 11 (note): the pending ND scheme fits as a third instance without new generic machinery. It is two consecutive `CodeTable2` tables, false choice first, with guard `702 · (n + 1)`, skipped by `codeSkipTable2` twice, and `codePrimRepeat` + `codePrimSkipTable2` for `exists_canonizer` | **Carried** into the `NDCodes` group-C fill (`exists_effectiveNDMachineCode`), now unblocked; it rides the next epoch that takes `NDCodes` |
| 13 (note): CH34-D2 is discharged under the approved residuals; adaptations 23 → 1 (`zfBFallback`); keep the serializer watch item | **Recorded**: the ledger's CH34-D2 row is marked discharged, with the verified delta, and the serializer resemblance stays a watch item |
| 15 (note): the stale legacy BridgeExport program | Already backlog **H-1** |
| 1–10, 12, 14, 16 (notes) | Freeze, abstraction, instances, moves, docstrings and the evidence limits all confirmed. No action |

**Gate CLOSED. PR #19 is clear to merge.**
