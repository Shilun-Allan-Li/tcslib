# 12.2c T1 item 7 (CH7-D1) gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 3 minors, 17 notes

Findings verbatim in `audits/12.2c-t1-blockloop-findings.md`. Pack:
`audits/12.2c-t1-blockloop-pack.md`. The auditor reconstructed every
after-source from the patch. It confirmed the 26 frozen public statements, the
20 new publics, the instance map and the OR-via-zero-mask derivation on
malformed inputs, and reproduced all six screens. **CH7-D1 is discharged.**

| Finding | Disposition |
|---|---|
| 1 (minor): `BlockLoop.polyTimeComputable_step`'s docstring calls the two emptiness guards disjoint, but both fire at `blockDone` | **Swept** (comment-only): "one `ite` on the disjunction of the two emptiness guards" |
| 2 (minor): `polyTimeComputable_xorD`'s sketch states the round budget as `\|z\|+1` | **Swept** (comment-only): the budget is the normalized pair's length plus two, `(pairEncode (pairFstD z) (pairSndD z)).length + 2`. `PolyTimeBlockLoop.lean` is comment-stripped identical and re-checks at 0 errors |
| 3 (minor): the baseline cross-file count is 64, not 65 | **Corrected** in `briefs/ch34-t1-item7.md`. The agent's report is an archived delivery artifact and is left as delivered; the integration record and the pack already carry 64 |
| 13 (note): `orbit`, `iterate_done`, `flatMap_emit_orbit` and `polyTimeComputable_orLoop` are not hypothesis-minimal | **Carried** as possible future weakenings (backlog). The frozen interfaces are correct as they stand |
| 17 (note): the old `length_xorPairStep_le`/`length_sliceDropAt_le` near-copy remains, excluded by the brief | **Carried** in the ledger as residual accounting; not described as duplication-free |
| 18 (note): optionally enumerate the comment-only section-header edits in such briefs | Adopted for future briefs |
| 4–12, 14–16, 19–20 (notes) | Confirmed. No action |

**Gate CLOSED. PR #18 is clear to merge.**
