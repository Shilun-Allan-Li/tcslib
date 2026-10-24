# The phase host's last phase (PR #156, an API gate): resolutions (round 1 FAIL, fixed; round 2 PASS; gate CLOSED)

**Gate:** the API gate of PR #156 (`lean/phasehost-last` at `a4d9b024`: `0b671a28`, the
maintainer's rewrite of `phaseHostTM_run` `9f82de74`, and two merges of the campaign branch, after
#154 and #155). Pack `pack.md`; bundle SHA-256
`87d56842f52d8b021e6fe7a92b3a75f6c72dcccdf8123e32dfc2249c57993b83` (150 sections; folder
`69-phasehost-last-api-gate/`), built from the Lean files at `a4d9b024` and the records at
`4fc5a7b5`. Replay `replay-lphl.sh` passed (user, 2026-10-23): 88 of 88 at `a4d9b024`,
static-equal (53). By the user's ruling of 2026-10-23 the gate was dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-23, SHA-256
`a1ef694a44531ee0291fd3e42efc6701a9fbce3c779ccc818ceb0d99387c4d0a`): **FAIL, 0 blockers, 1 major,
1 minor, 8 notes.** The maintainer checked both actionable findings directly: both true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | Six older proofs in four files re-derive the newly published prefix argument (`wr_prefix`; `recordSkipTM_tail`; `b2b_trial_run`'s `hpz`, `b2b_round_run`'s `hprefix`, `b2b_finish_answer`'s `hp`; `canonEmitVerdict`'s `leaf`); the text screen does not establish semantic reuse. | **True.** Each site proves the tagged-run prefix through `MultiTapeTM.runFrom_mapState_of_agreeOn`, its table agreement closed by unfolding `phaseHostTM` in another file (`simp [… phaseHostTM …]` in `wr_prefix` and the three `Inclusions` sites, a definitional `rfl` in the other two). All six predate #156. The pack's search (files using both `phaseHostTM` and the transfer) found the files but read only for restated statements. **Ruled (user, 2026-10-23): fix it in #156.** Commit `0e5f210b`: each site is now an application of `Turing.phaseHostTM_run_le` with its local guard conversion. A wider search for other-file `phaseHostTM` unfoldings found a seventh site of the same kind, `OracleSim`'s `oracleHost_offQuery`, whose table agreement off the query state re-derived `Turing.phaseHostTM_tr_of_red_none`; it is now that lemma. Statements unchanged; proofs and the sketches of `wr_prefix`, `recordSkipTM_tail` and `oracleHost_offQuery` only (`evidence/round1-fix/`). A seal sweep of all 16 other files that use the host (`phaseHostTM` irreducible) and the search for explicit unfoldings find 12 older one-field or one-step reads in seven files: the start state, the redirect branch's dispatch, single table reads, and `phaseHostND_fixChoice` (`evidence/round1-fix/phasehost-reads-inventory.md`). None is a prefix or a table agreement for a run; most need equations that are not published. **Ruled (user, 2026-10-24): a follow-up API PR after #156** (a start-state and a redirect-branch equation in `Build/Seam`, and the re-points, with their own gate and replay), landing before megafill C is issued. `hprefix`'s start configuration `d` is the tagged `c` by definition, as before. Round 2 audits `0e5f210b`. |
| 2 | minor | The PR body says "Seam and the six files" where the population has seven; the lint log is of the 905-line first head, not the final 919-line `Seam`. | **True; records.** The PR body now says seven files. The lint records are re-run at the round-2 head (`evidence/round1-fix/lint-*.txt`, which list `Seam` at 919 lines); `lint-build.txt` stays as the first head's record. |
| 10 | note | The replay is a separate merge condition. | **Agreed.** The round-2 head's replay is `replay-lphl2.sh`: the five changed files' downstream closure (23 modules), chained from `oleans-lphl`. **Passed (user, 2026-10-24): 23 of 23**, 0 failed, static-equal (27) (`evidence/round1-fix/replay/`). |
| 3–9 | notes | Integrity and the freeze; the table equation; the run lemma's boundary cases; sufficiency (no dispatch form needed); the rewrite of `phaseHostTM_run`; the elaboration, axiom and seal records; the screen. | No action. Note 9's distinction between text-screen results and semantic duplication review is kept in the round-2 pack. |

**Round 2** (`pack-r2.md`; bundle SHA-256
`2ca0c3c6660f6dc6663a558e17dd7913734c75317c1a0863577f8c7d32bf05a6`, 100 sections; folder
`69-phasehost-last-api-r2-gate/`, built from the Lean files at `0e5f210b` and the records at
`1b02da22`): a re-audit of `0e5f210b`, dispatched before its replay.

**Round 2** (`findings-r2.md`, verbatim; received 2026-10-24, SHA-256
`91e6fe20688b2b4763d6e106ed52848c8ec8ebbfdf7fc3074fc91e8b7cee42a3`): **PASS, 0 blockers, 0 majors,
1 minor, 10 notes. The gate is closed.** The maintainer checked the minor directly: true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `Inclusions`' private census omits six unchanged anonymous instances (the `Fintype` and `DecidableEq` instances of the test, body and host phase families): 4 public / 70 private, 74 in all, at the base and the head. | **True; erratum.** `declfreeze.py` counts named declarations only; the six instances (lines 520–621) are byte-identical at the base and the head. The pack's and the freeze record's 4/64 (68) read as named-declaration counts; the full census is 4/70 (74), unchanged. |
| 6 | note | The seal certifies the replacements, not `hprefix`'s older conversion of `d` to the tagged `c`. | **Agreed;** as disclosed. |
| 7 | note | Four of the twelve remaining reads already have the published table lemma available; all twelve stay in the follow-up. | **Agreed;** the inventory says so, and the follow-up (prepared locally, `local/phasehost-fields`) uses `phaseHostTM_tr_of_red_none` for them. |
| 10 | note | Keep the screen claim distinct from semantic completeness; the PR body's all-branches absence claim is not independently established. | **Agreed;** #156's description now qualifies it by the searches made (the campaign branch and the open PR heads at the time) and points to the semantic inventory. |
| 11 | note | Record the round-2 replay before merging. | **Done:** `replay-lphl2.sh` passed (user, 2026-10-24): 23 of 23, 0 failed, static-equal (27) (`evidence/round1-fix/replay/`). |
| 2–5, 8, 9 | notes | Integrity and the freeze; the unchanged API; the six prefix re-points; OracleSim's table equation; the elaboration and axiom records; the records minor's repair and lint. | No action. |

**Merge state. #156: clear to merge.** Both rounds are audited and the gate is closed, the round-2
replay has passed (the round-1 replay too, 88 of 88), and the base is the campaign branch (whose
Lean content is unchanged since #156's last merge of it).
