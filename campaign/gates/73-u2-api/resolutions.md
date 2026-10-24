# U2's API (PR #161, an API gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the API gate of PR #161 (`lean/u2-api` at `a8c45ad7`, one commit on the campaign
branch, Lean tree `21d53053`). Pack `pack.md`; bundle SHA-256
`08c83e404b4c7f3e19cb78674c2a4f548f0687831e748e8d8bd7d81e8ea12251` (80 sections; folder
`73-u2-api-gate/`), built from the Lean files at `a8c45ad7f176f0ba833fe5feee0fb5d96fecb76b` and the
records at `43260da4204e1243f143774c304c443f50132134`. Dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-24, SHA-256
`acaf30c4663d14cf03f574506ea47fdb545078e28cff878b7048ab05cabf2373`): **PASS, 0 blockers, 0 majors,
3 minors, 9 notes. The gate is closed.** The maintainer checked the three minors directly: all
true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `Deterministic`'s vendored header does not list the new `spaceUsedByTape_eq_card` among the local modifications (`policy.md` §2). | **True; fixed.** Commit `4e9a46be` on #161, comments only: the header's list gains the entry beside `spaceUsed_eq_sum`'s. The code is identical with comments stripped; the file elaborates with no diagnostic against `oleans-lphf` (`evidence/round1-fix/`). A comment-only change needs no gate. |
| 2 | minor | The replay driver checks the pre-merge API head, not the merged candidate the pack requires after #158–#160. | **True; planned.** After #160 merges, the campaign branch is merged into #161 and the replay is regenerated against that merged head (the three audited blobs pinned, the base the campaign tip, chained from the latest merged-tree snapshot); its head and result are recorded here before merge. |
| 3 | minor | The space probe seals `spaceUsedByTape`, `visitedByTapeHead` and `spaceUsed` but controls only the first. | **True; fixed.** `evidence/round1-fix/U2SpaceProbe2.*`: the same probe on the head's `Deterministic` with two more controls, `visitedByTapeHead`'s defining equation and `spaceUsed`'s sum equation. Unsealed all four controls close; sealed exactly the four fail (lines 578, 583, 589, 593); both ledger steps still close sealed through the new equation. |
| 9 | note | Use the tested consumer forms when updating the U2 draft; rerun its issue-time checks. | **Agreed;** at U2's issue (megafill C) the draft's route probe is rewritten against the generated names (`funext` before the pointwise tape equations, `.val` through `rulerHostCfg_inputPos`) and its pre-ship re-run. |
| 10 | note | SD-1 is fully disclosed and acknowledged; follow its disposition; add no U2-local suffix drop. | **Agreed;** the U2 brief cites `Turing.pairEncode_drop`. |
| 11 | note | Keep command, status and fresh-output evidence with the merged-tree replay. | **Agreed.** |
| 4–8, 12 | notes | Integrity and freeze; the two encodings' equations; the pairing drop; the cardinality equation; the consumer probe; lint. | No action. |

**Merge state. #161: not yet clear to merge.** The gate is closed; the merged-tree replay (325
modules) runs after #160 merges.
