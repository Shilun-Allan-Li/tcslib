# C1, the replay canonizer (PR #160, a fill gate): resolutions (round 1 FAIL, fixed; round 2 PASS; gate CLOSED)

**Gate:** the fill gate of PR #160 (`lean/c1-replaycanon` at `73c99430`: the review's proof landed
directly, by the user's ruling of 2026-10-24). Pack `pack.md`; bundle SHA-256
`f39f1480a00f20aeb6ca6c808bcfbca176bfbcd1a736bc620bce52a3ca57d693` (114 sections; folder
`72-c1-replaycanon-fill-gate/`), built from the Lean files at
`73c99430045d253939ea7e21aef609dec63de647` and the records at
`af405e14fb1efc0f9630084e909e93a1fa1723a7`. The replays: `lrcan` (4 of 4, on #156's tree) and,
after #158 and #159 merged, `lrcan2` (4 of 4, on #159's tree; the campaign merged in at
`dd7b126a`).

**Round 1** (`findings.md`, verbatim; received 2026-10-24, SHA-256
`b1166345d9b8a3291895ea442dfb67628273a6c5d3738e0ebe80b664122905d7`): **FAIL, 0 blockers, 1 major,
1 minor, 11 notes.** The maintainer checked both actionable findings directly: both true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The private `rc_workReads2_length` re-proves `(workReadsK 2).length = 9`, the `k = 2` case of the published `Turing.StepBlock.length_workReadsK` (`(workReadsK k).length = 3 ^ k`), against the draft's "cite proved material; never re-prove it"; the text screen missed it. | **True; fixed.** Commit `4cb0c670`: its proof is `rw [StepBlock.length_workReadsK]` and `rfl` (core's `3 ^ 2 = 9`), its docstring names the lemma; the statement and its one use are unchanged. |
| 2 | minor | The private abbreviation `RcT` breaks the file's `rc_` prefix rule. | **True; fixed** in `4cb0c670`: renamed `rc_State`, with its eight uses. |
| 13 | note | Optional: keep per-input blob hashes with future screen runs. | **Agreed;** screens now read dedicated, unmoving worktrees (the base on a detached `wt-screenbase` at the campaign tip), whose status line records the revision. |
| 6, 10 | notes | The boundary cases and the screen's three new pairs (harmless proof idioms; finding 1 is separate). | **Agreed. Ruled (user, 2026-10-24): accepted as idiom pairs** (`rc_replay_table` and `rc_workReads_snoc` against `StepBlock`'s `tableBitsK_groups`, 62% and 55%: a shared `simp only` list of `List.flatMap` rewrites, different statements); no ledger entry. |
| 3–5, 7–9, 11, 12 | notes | Integrity and freeze; the definitions; the correctness argument; the composition; primitive recursiveness; rule 10 and 11; the execution evidence; the prose and lint. | No action. |

**The fix** (`evidence/c1-replaycanon-landing/round1-fix/`): `4cb0c670` on #160, then the campaign
merged in (records only, `1cc8ab39`). Against `oleans-lphf` (#159's tree): `NDCodeSimulator` with
no diagnostic; the round-1 seal (21 definitions, 22 controls) re-run on the fixed file: its only
errors are the 22 controls (lines 89–166), the home from line 168 elaborating sealed; the
canonizer, the core and the bridge on the standard three; against round 1's head: 3 → 3 public,
49 → 49 private (`RcT` removed, `rc_State` added; `rc_body`'s statement renamed only;
`rc_workReads2_length`'s body changed); lint 0 FAIL, 68 WARN. Replay `replay-lrcan3.sh`, the 4
modules from `oleans-lphf`: **passed (user, 2026-10-24): 4 of 4**, static-equal (1); the universal
NDTM on the standard three on `oleans-lrcan3`. Screen: the tip 541/173, the head 565/176; against
round 1's head no pair new or gone. Round 2 (`pack-r2.md`) audits the fix.

**Round 2** (`pack-r2.md`; bundle SHA-256
`bfbee60b142d80b8106b338c7de9784e43f9aa5a8ac25c2b0bd0e9df1675ee96`, 73 sections; folder
`72-c1-replaycanon-fill-r2-gate/`, built from the Lean files at
`1cc8ab3964d63694915297f855dc758458f2d37d` and the records at
`3b0950f00d19a84bbf7e1f63ccacf3d94c4331af`).

**Round 2** (`findings-r2.md`, verbatim; received 2026-10-24, SHA-256
`96f4b9093f927a796962f5b72c461db915670f3d1f0923ba7eaa2c377621967e`): **PASS, 0 blockers, 0 majors,
0 minors, 10 notes. The gate is closed.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 2, 3 | notes | Round 1's major and minor are resolved. | No action. |
| 10 | note | Record the promised idiom-pair disposition when closing. | **Done:** ruled (user, 2026-10-24), accepted as idiom pairs (round 1's row for notes 6 and 10, `fcb259c5`, after this round's records commit). |
| 1, 4–9 | notes | Integrity; the freeze; the seal; elaboration and axioms; the replay; the screen; lint. | No action. |

**Merge state. #160: clear to merge.** Both rounds are audited and the gate is closed, the replay
on the tree after #159 has passed (`lrcan3`, 4 of 4), and the base is the campaign branch (whose
Lean content is unchanged since #160's last merge of it).
