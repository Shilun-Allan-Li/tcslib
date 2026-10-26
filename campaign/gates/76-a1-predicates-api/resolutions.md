# A1, the chapter predicates' readings (PR #164, an API gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the API gate of PR #164 (`lean/a1-predicates` at `ae4849af`, one commit on the campaign
tip `39c649e6`, Lean equal to #161's merged tree). Pack `pack.md`; bundle SHA-256
`e3899cfd188ec16d63fd341e8691a4a5d1bdecb1967f9d473d5db4d1d38a0bc2` (50 sections; folder
`76-a1-predicates-api-gate/`), built from the Lean files at
`ae4849afd7f94cdc0890a12ed5c50ea9e075533c` and the records at
`8c247ccb199715c263315db0b71fe755eed29533`. Dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-25, SHA-256
`31375e719e1b12e78adf943193c896fa10d1add84994d3460fb72132303c04d8`): **PASS, 0 blockers, 0 majors,
0 minors, 14 notes. The gate is closed.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 7 | note | `transduce_of_copy` generalizes both published instances; keep their re-pointing in the 12.2c window. | **Agreed; recorded.** The ledger had no row for the family (the review's "the ledger names the two instances" was not carried out when A1 opened). It now does: **TC-1** (`campaign/duplication-ledger.md`), with the ruling and the census (Transducer 1 of 10, KarpLiptonPrefix 1 of 16, MeyerVerifierGlue 1 of 42). |
| 8 | note | No further reading is needed; carry the corrected dominance citation and the fill-appendix requirement into the eventual fill; do not describe E-Q's witness probe as a machine construction. | **Agreed, with a change of vehicle for SCP.** The user ruled (2026-10-25) to land `spaceConstructible_poly` directly, from the consumer probe, instead of by a fill. The landing (`lean/scp-landing`, stacked on #164) cites `Complexity.logSpace_le_succ` for dominance and not `logSpace_eq`. Its code is the probe's route, identical with comments stripped. A maintainer landing is not bound by a frozen docstring, so the docstring's proof sketch is rewritten to the route taken, in place of a fill appendix. E-Q's brief, when drafted, will describe its witness step as a probe of the reading only, with the machine assembly still open. |
| 9 | note | Retain the name-scan attestation with its limitation (not rerun by the audit). | **Agreed.** |
| 11 | note | Retain the distinction between checked logs and a fresh elaboration. | **Agreed.** The elaboration evidence is the maintainer's; the merged-tree replay (item 14) is the fresh run. |
| 12 | note | `SPACE`'s remaining check-8 warning is a false positive (`mem_SPACE_iff`). | **Agreed;** no action. |
| 14 | note | Run and record the 193-module replay on the integrated tree after #162 before treating A1 as cleared. | **Agreed;** it is A1's merge condition. The closure includes the `TuringMachine` facade, which #165 also edits, so if #165 merges first, the replay is the merged-tree union from the last common snapshot. |
| 1–6, 10, 13 | notes | Integrity; the readings' faithfulness (time and space constructibility, `ComputesInSpace`, `DecidesInSpace`, `SPACE`, `logSpace`, `LOGSPACE`, the transducer); the freeze; boundary checks. | No action. |

**Merge state. #164: not yet clear to merge.** The gate is closed. The merged-tree replay is
outstanding. After #162 and #165 merged, the campaign was merged into #164 (2026-10-26; head
`1ff735f8b31a0770ba954ef3e39cd95dcaa67a8e`, Lean diff from the campaign tip `f0df8ee5` exactly the PR's
four files). `replay-la1m` (`evidence/merged-tree/`) replays their downstream closure, 193
modules, chained from `oleans-lg4c4m` (the campaign's tree after #165); its precheck passed. A
trial merge before #165 landed gave the same list. #164 goes first: its snapshot then carries
#167's 91-module replay, #166's 2-module replay and the A+ PR.
