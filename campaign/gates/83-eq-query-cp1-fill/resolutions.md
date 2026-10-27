# E-Q checkpoint 1, the guard and the reduction (PR #173, a light fill gate): resolutions

**Gate:** the light fill gate of PR #173 (`lean/eq-cp1-landing` at `599497bc`). Pack `pack.md`;
bundle SHA-256 `49035558e2071cd46f41843727c152297c663fa573b8a3d0518ce104052330cf` (46 sections),
the records at `669fcca6`. **Findings** (`findings.md`, verbatim, SHA-256 `c3195990…`; received
2026-10-27): **PASS, 0 blockers, 0 majors, 1 minor, 14 notes.** The gate is closed.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The seal generator's diagnostic prints `controls 40`; the generated controls are 31 delta, 4 simp and 4 usage, 39. | **True; fixed** in `evidence/scripts/mkseal_v2.py` (`evidence/round1-fix/mkseal-count.patch`; the scratch copy too). The line now counts the generated `#rfl_control`, `#simp_control` and `example` lines. Re-run on the head blob `f965eac0` with the worker's 29-name list, it prints `controls 39`. The sealed and unsealed sources are byte-identical to `evidence/lwords/EQSeal_*.lean.txt` (`evidence/round1-fix/regen.txt`). Only the diagnostic changed: the pack, the summaries and the raw outputs already said 39. |
| 2 | note | Integrity and provenance verified. | Agreed. |
| 3 | note | Scope, authorship, freeze and source census agree with the pack. | Agreed. |
| 4 | note | The definitions' meanings are preserved; no new definition or import cycle. | Agreed. |
| 5 | note | `qy_guard` holds with no assumption on `f` or `g`. | Agreed. |
| 6 | note | The three cuts implement the guard in linear time. | Agreed. |
| 7 | note | `qy_query_of_main` has the stated output and a uniform bound. | Agreed. |
| 8 | note | The remaining contract is the brief's total main-machine interface; its boundary cases are sound. | Agreed. Cont1's brief states the same totality: `hmain` must compute the unary query on every word. |
| 9 | note | The published word tests are consumed as published; the private re-derivations are gone. | Agreed. Cont1's pre-ship re-took the same 30-file screen on the landed tree: 1,735 declarations, 2,152 pairs, none with an owned-file declaration (`campaign/fills/eq/drafts/eq-fill-query-cont1/preship-599497bc/`). |
| 10 | note | Rule 10 is supported by effective controls and source inspection. | Agreed; finding 1 fixed. |
| 11 | note | The actual-import evidence supports the head; the prepared evidence is historical. | Agreed. `evidence/lwords/` is the current-dependency evidence, and the replay below re-elaborated the head. |
| 12 | note | The new docstrings and the status paragraph are accurate and public-facing. | Agreed. |
| 13 | note | The historical evidence corroborates the review, with its limits and the warning correction. | Agreed. The review's F8 (the 501-name probe's one deprecation warning, against the worker report's "zero … warnings") stands in the review's records. Those records give the archive hashes and member checks as the maintainer's execution evidence, not as checks the auditor reproduced. |
| 14 | note | The admission boundary is exactly the authorized one; neither open theorem is presented as proved. | Agreed. `hmain` goes verbatim to cont1 (`campaign/fills/eq/drafts/eq-fill-query-cont1.DRAFT.md`); `exists_diagonalizer` is E-D's. |
| 15 | note | The replay is pending; complete the two-module replay before merging, and recompute its scope if the merge base changes. | **Done.** `replay-leqcp1` passed before these findings arrived (below). The merge base has not changed: the campaign has had no Lean change since #173's merge-in, and `git diff` between the campaign tip and `599497bc` over `TCSlib/` is `NTimeDiagonalizer` alone. |

**The replay.** `replay-leqcp1` passed (user, 2026-10-27): 2 of 2 modules at `599497bc`, 0 failed,
static-equal (0 mismatches; `NTimeDiagonalizer`'s two sorries are the target and
`exists_diagonalizer`; `evidence/merged-tree/replay-leqcp1.log`, `replay-leqcp1-static.txt`). Its
snapshot is `oleans-leqcp1`.

**Merge state. #173: clear to merge** (2026-10-27) at
`599497bc69889781f34b1925c8772b3645b00608`:
- **The gate:** passed, 0 blockers, 0 majors.
- **The replay:** passed at that head.
- **The base:** the campaign branch, with no Lean change since the merge-in.

Merge #173 before #172: #172's replay is chained from `oleans-leqcp1` and needs #173's
`NTimeDiagonalizer`.
