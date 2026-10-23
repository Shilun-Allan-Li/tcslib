# The input rewind as a machine (PR #153, an API gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the API gate of PR #153 (`lean/input-rewind-api` at `ac5ce7bc`, one commit on the
campaign branch at `86523ba5`). Pack `pack.md`; bundle SHA-256
`0dca1496976784e37d055ce2d4229eae68c0da18da0f5725edd28baecba3fe16` (69 sections; folder
`65-input-rewind-api-gate/`), built from the Lean files at `ac5ce7bc` and the records at
`d6b2ed92`. By the user's ruling (2026-10-23) it was dispatched before the post-#149 replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-23, SHA-256
`3b2123cc3fa04b812af451f5939c411f51badf7851967497ff5ebc342b3e35ff`): **PASS, 0 blockers, 0 majors,
3 minors, 10 notes. The gate is closed.** The maintainer checked the three minors directly: all true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The module overview omits `d.state = some .start`; the run's sketch says every left step reads an input symbol, but at `p = x.length + 1` the first reads the right blank. | **True; fixed.** Commit `1148924f` on #153, docstrings only: the overview says the run starts in the start state; the sketch makes the first left step unconditional and restricts the symbol-reading argument to `1 ≤ r < p`, where `1 ≤ p - r ≤ x.length`. The code is identical with comments stripped, and the module elaborates against `oleans-lu2sc1` with no output (`evidence/round1-fix/`). A docstring-only change needs no gate. |
| 2 | minor | The evidence index names attachments that are absent (the bundle's README, `replay-lirapi.sh`, its static check), so the records commit is not identified; the PR body keeps "gate after the replay". | **True; records.** The bundle was built from the records at `d6b2ed92` (the Lean files at `ac5ce7bc`). The pack's "stated in the bundle's README" pointed to a file outside the bundle. **From now on every dispatch prompt names both revisions.** The replay script, log and static check are written when #149 has merged and are added here then. #153's description is updated to the 2026-10-23 ruling and this result. |
| 3 | minor | IR-1 calls `un_mapState_comp` a restatement of `xr_E_initCfg`; their statements differ, and the 54% is shared field-equation proof text. | **True; ledger corrected.** The ledger now says the two share field-equation proof text, and that the composition lemma alone does not replace `xr_E_initCfg`; the dedup review stands. |
| 8 | note | Rule 10 is supported; describe `Cfg.init` accurately as an additional simp erasure. | **True; erratum.** The pack's "the two `@[simp]` definitions among them (`Action.apply`, `Cfg.init`)" is inexact: `Cfg.init` is not one of the seven irreducible definitions; the stronger variant erases it, with `Action.apply`, from the simp set. |
| 10 | note | Placement and naming follow the design; a documentation cross-reference from `StateRenaming` would aid discovery. | **Agreed; backlog** (optional, with `StateRenaming`'s next change, since an edit there replays its closure). |
| 11 | note | #152's copy (`canonGramMapComp`) awaits its own disposition. | **Ruled (user, 2026-10-23): re-pointed at #152's landing**, prepared and part of gate 67. |
| 13 | note | The pending merged-tree replay is a separate merge prerequisite. | **Agreed.** After #149 merges: merge the campaign branch into #153, replay the closure (`down-lirapi.txt`) from #149's merged-tree snapshot, and record the merge head, the snapshot, the closure check and the replay. |
| 4–7, 9, 12 | notes | Integrity; the definitions and contracts (adversarial cases included); the composition law; the API's sufficiency for the exhibited consumers; NDHost's exact re-point; lint. | No action. |

**Merge state. #153: not yet clear to merge.** Its replay runs after #149 merges.
