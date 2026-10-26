# §13d G4 continuation 4, the G4 landing (PR #165, a fill gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the fill gate of PR #165 (`lean/g4-cont4-landing` at `37fe114e`: the delivery's 37
commits, the landing edits `4d69c096`, the 83 proof sketches `292acad2`, and a records-only merge).
Pack `pack.md`; bundle SHA-256 `9e2b1a347cec255a6a8a3ac8cb98743bfc10e5c0e71290c2072dcfe14d44275b`
(64 sections; folder `75-s13d-g4-cont4-fill-gate/`), built from the Lean files at
`37fe114ef6f05548455ccefb27cea1f9a726f9d9` and the records at
`cf99f7a058fa542edcd2b851547ec20526126c23`. Dispatched before the replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-25, SHA-256
`97ef47df9b3b1097e80c09178289fe1721525c33886aed431c4d1a103caa2058`): **PASS, 0 blockers, 0 majors,
6 minors, 11 notes. The gate is closed.** The maintainer checked the six minors directly: all
true. Minors 1–4 are errors in sketches that the maintainer wrote for the landing (F3's 83 and B2).
They are fixed by two docstring-only commits on #165, `844c85e8` and `78e6c53f`
(`evidence/round1-fix/*.patch`). The code is identical with comments stripped against the audited
head (`codeonly-37fe114e-vs-78e6c53f.txt`). At `844c85e8` the file elaborates against
`oleans-lu2api` with no diagnostic: 185 s, 3.6 GiB (`elab-ZoneRebalance-844c85e8.*`). The second
commit edits only the same docstring. Docstring-only changes need no gate. Minors 5 and 6 are
records.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `zr_leftWalk_fields`'s sketch reverses the adjusted walk and misstates the word: the scratch step comes first, then the walk over the ruler's tail of `n − 1` cells. | **True; fixed** (`844c85e8`). The sketch now gives the scratch-only step, the dispatch, the lockstep walk over the tail (`List.length_tail`), and the time `1 + 1 + n`. |
| 2 | minor | Two seek offsets: the final seek's displacement is `2 · zoneStart (ℓ + 1) − 2`; B2's right seek stops at the second blank, `zoneStart ℓ`, not the separator. | **True; fixed** (`844c85e8`). `zr_finalContract`'s sketch gives the start `2 − zoneStart (ℓ + 1)`, the end `zoneStart (ℓ + 1)` and the displacement. In `exists_zoneExtendTM`'s implementation note (B2), the right seek stops on the second of the two consecutive blanks, the new zone's first cell, and the note says that the plan names the separator. The frozen fill-plan sentence is unchanged. The paragraph is rewrapped. |
| 3 | minor | `zr_hmSc1`/`zr_hmSc2` attribute the writes to the one-cell leaf; they are `zr_pinCopy_step` mapped copies, and the clears are the clear contract. | **True; fixed** (`844c85e8`). Both sketches attribute the tape-`0` writes to single-cell mapped copies (`zr_pinCopy_step`, steps 19, 25, 27 and 37, 42), the scratch erasures to `zr_pinClear_step`, and the head moves to non-writing one-cell steps (`zr_pinCell_step`) and the back skip. The step lists are checked against the code's step comments. |
| 4 | minor | `zr_fpSeg_time`'s sketch omits the walk-out's escape round and the two control steps per round. | **True; fixed** (`844c85e8`, `78e6c53f`). The sketch now states: two control steps per round; the pass bound `2a · 2^h + (b + 2) r` for `r` rounds with highest level `h` (`zr_pass_time_desc`/`asc`, as stated); the walk-out's `n + 1` rounds and its bound `4 · 2^n + 13(n + 1)`; the other six passes' `n` rounds; the fifteen pop and dispatch steps; and the aggregate `268 · 2^n + 728 n + 183 ≤ 1000 · 2^n + 200`. The figures are checked against the proof's `k1`–`k9` and its final `show`. |
| 5 | minor | RI-1 records only the copy side's census. | **True; fixed** (`campaign/duplication-ledger.md`, RI-1). The source side is added: `Build/Contract/Basic` 1 of 85 declarations (84 public and 1 private, per the lint; the finding's 1/84 counts the publics), the public `Turing.Round.iterate`, 18 lines with its docstring, 1.2%. The one-fifth rule is not reached. The ruled follow-up, the sequence-form API PR, stands. |
| 6 | minor | 173 of the 500 pairs are justified only by class in undelivered reports; the checkpoint zips are absent. | **True; fixed for the pairs; recorded for the artifacts.** `campaign/fills/s13d/reviews/g4-cont4/pair-dispositions-zips1-3.md` now gives each of the 173 its own row: share, zip, classes, statements and longest shared tile. They were recomputed with the screen's own extraction and tiling (`scripts/classify.py.txt`; `out/44-zips1-3-pairs-classified.txt`), and all 173 reproduce the worker's figures exactly. No pair has two declarations with the same statement. The 13 pairs between `def`s share only their binders, since their types are inferred. Every pair falls in a scaffolding class: contract openings 146, `Cfg.ext` field branches 142, zone-layout readings 39, arithmetic openings 15, word readings 6, instance plumbing 4, phase literals 4. Each row's disposition: in-file scaffolding between sibling declarations with different statements, not a ledger member. **Unavailable artifacts (recorded honestly):** the worker's zip-1–3 reports and the checkpoint zips were never delivered. The checkpoints exist as commits in the delivered series, and the review elaborated six of them (`out/30-*`). No history rewrite or proof change. |
| 15 | note | The landing's peak memory is 3.40 GiB in binary units, not the pack's "3.6 GiB". | **Agreed;** the pack's figure was 3,645,554,688 bytes as decimal GB. This round's elaboration: 3,861,348,352 bytes (3.6 GiB). |
| 16 | note | Keep the replay host's headroom of at least 5 GiB. | **Agreed.** |
| 17 | note | Run and keep the two-module replay at the applicable landing or merged snapshot. | **Done at `37fe114e`:** `replay-lg4c4` passed, 2 of 2, static-equal (`campaign/fills/s13d/evidence/s13d-g4-cont4-landing/replay-lg4c4.log`; the snapshot `oleans-lg4c4`). The head has since moved by the two docstring commits. If #162 merges first, #165 will also need a campaign merge. Either way the merged-tree replay is rerun at the final head before #165 is clear. |
| 7–14 | notes | Integrity; the frozen interface; extension at `C = 135`; rebalance at `C = 2300`; the three route deviations; rule 10's seal; duplication; sketch coverage (beyond 1–4). | No action. |

**After #162 merged (2026-10-25):** the campaign branch was merged into #165 (`308838e5`; the facade
auto-merged, the two edits in different lines). Its Lean diff from the campaign tip `5a258cc2` is
the facade and `Build/ZoneRebalance`. The merged-tree replay `replay-lg4c4m` is written for that
head: the same two modules, chained from `oleans-lkit2` (the campaign's tree after #162), with the
two blobs pinned. **Passed** (user, 2026-10-25): 2 of 2, 0 failed, static-equal
(`campaign/fills/s13d/evidence/s13d-g4-cont4-landing/merged-tree/replay-lg4c4m.log`, `-static.txt`;
the snapshot `oleans-lg4c4m`, the campaign's tree after #162 and #165).

**Merged (user, 2026-10-26)** as `f0df8ee555dbaa29befbe7ab576e17ccd656c49c`. The campaign's TCSlib
tree after the merge equals the replayed head `308838e5`'s, so `oleans-lg4c4m` is the campaign's
snapshot after #165. #167 is retargeted to the campaign branch. Before the merge:
**#165: clear to merge** (2026-10-25). The gate is closed. The merged-tree replay
passed at the head `308838e5`, and the PR's base is the campaign branch, whose Lean has not moved
since #162's merge `5a258cc2`. Its stacked follow-up #167 is retargeted after the merge.