# #118 round-3 gate review: the brief-inventory API (PASS 0/0/2, records only)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad.

**Inputs:**
- The findings `audits/brief-api-r3-findings.md` (SHA-256 `c337232d…6dc2`), read as data.
- The bundle (SHA-256 `2b75b765…6c9a`), verified.
- The Lean at `531b98a2` (`origin/lean/brief-api`).
- The records at the campaign tip `e5b5e6f9`, after a `git fetch`. It contains `2adfd457`, and its two extra commits touch only `audits/brief-api-r3-findings.md` and `backlog.md`.
- The records were extracted with `git archive` into `$S/review/bapi-gate-r3/rec/`.

No elaboration was needed, and no worktree other than my own was touched.

**Ready to close the gate: zero blockers, zero majors. The two minors are records only.**
**Ready to merge: #118 at `531b98a2`. `gh` reports it open and `MERGEABLE`.**
- The tip has no Lean change since the merge base `bd1ae147`.
- `git merge-tree` is clean.
- The 320/320 replay therefore covers the merged Lean.

## (a) Verification

| Claim | Check | Result |
|---|---|---|
| Round-3 Lean = the reviewed patches | `git diff 4624fc05 531b98a2` touches exactly Catalog, CounterLoop, Configuration and Deterministic. Their blobs at `531b98a2` are `c2802df7…`, `963a97ec…`, `a9f14a78…`, `efd291b1…`: the reviewed blobs and the replay pins. | ✓ |
| The eight equations' formulas | The `r3/logs/Probe*.out` types match the auditor's restatements: the four `Action.apply` fields; `step_of_some` and `outputSymbol_of_some` (with `cfg.state = some q →`); `counterWord_succ`; and `scanResult_keep_keep` (`= (a₀, w)`). Axioms are `[propext, Quot.sound]`, and `[propext]` for the identity scan. | ✓ |
| Ledger 173 = 76 + 97 | The tip ledger is 175 lines (2 header + 173). It is the same blob (`bef89a48`) as my review output, built from 76 explicit and 97 implicit rows. | ✓ |
| Replay 320/320, static-equal 94 | The tip's `r3/replay-lbapi4.log` header says `at 531b98a2`. It has `# modules=320 failed=0`, 320 `exit=0 errors=0` rows, and per-module sorries summing to 94. Its module order equals `replay-order-4.txt`, byte-identical to my `down-lbapi4.txt`. `replay-lbapi4-static.txt`: `modules 320, mismatches 0, static total 94`. | ✓ |
| No new screen pair | The tip's `r3/screen/screen-r3.txt` is byte-identical to mine. Base vs round 3: 798 → 799 declarations, and the pair lines are identical (487 pairs, 139,742 characters). | ✓ |
| **Minor 1** (stale re-point text) | All three ledger copies are blob `bef89a48`: `r3/unfold-sites-r3.tsv`, `r3/review-out/unfold-sites-r3.tsv` and `drafts/mig12-fill/unfold-sites.tsv`. The rows for CfgRecord 529 (`counterWord`) and 1189 (`scanFold`, `scanKeep`) still cite the pre-patch-2 interfaces. This is my generator's error: its re-point map was written before patch 2. `review-out/unfold-sites-r3-summary.txt` has no re-point column and is unaffected. | **true** |
| **Minor 2** (probe counts) | `MIG12ImportProbe.lean.txt` has 227 distinct `#check`s (219 + round 3's 8). `B6F5ImportProbe.lean.txt` has 58 (52 + round 3's 6, in a new eighth group). The `r3/draft-probes` outputs print 227 and 58 names with 0 errors. The drafts and the README still say 219 and 52. | **true** |

## (b) Closing and merging

- **The gate can close.** It is PASS, 0 blockers and 0 majors. Both minors are corrections to non-Lean records: commit them straight to the campaign branch (non-`.lean` rule).
- **#118 can merge** as soon as you choose. The minors do not block it, since they touch no Lean and no branch file.
- **After the merge,** issue the drafts with their tip base hash per the README.

## (c) Exact record fixes

**1. The ledger.**
- A ready corrected file is `$S/review/bapi-gate-r3/unfold-sites-r3.tsv` (blob `3768b9f8…`), made by an asserted scripted edit. Copy it over all three paths:
  - `audits/evidence/brief-api/r3/unfold-sites-r3.tsv`
  - `audits/evidence/brief-api/r3/review-out/unfold-sites-r3.tsv`
  - `audits/evidence/drafts/mig12-fill/unfold-sites.tsv`
- The changes, all in column 8 ("re-point to") unless noted:
  - **File line 7** (`529`, `counterWord`, `recordStep_digits_succ`): `counterWord_zero/_length/_value` → `counterWord_succ, counterWord_zero (round 3)`.
  - **File line 46** (`1189`, `scanFold`, `recordStep_cell_shift`): `scanResult_fold (no own lemma)` → `scanResult_keep_keep (round 3)`.
  - **File line 47** (`1189`, `scanKeep`, `recordStep_cell_shift`): `scanResult_* (no own lemma)` → `scanResult_keep_keep (round 3)`.
  - **File line 1 (header)**, the auditor's qualification. "every site that unfolds" becomes "every detected site that unfolds", and this is appended: "; implicit rows are a lower bound inside a tactic block, and reducible abbreviations' definitional uses are not detected".
- I also corrected the generator's map (`review/scripts/ledger_build.py`), so a rebuild gives the same three rows.

**2. The probe counts** (lines at the tip `e5b5e6f9`):
- `audits/evidence/drafts/mig12-fill-cfgrecord.DRAFT.md`:
  - **Line 101:** "(`MIG12ImportProbe.lean.txt`, 219 `#check`s)" → "(`MIG12ImportProbe.lean.txt`, 227 `#check`s; re-run against `oleans-lbapi4`, #118's round-3 replay; 219 before round 3)". Line 90's `oleans-lbapi3` stays as the snapshot of the other pre-ship measurements.
  - **Line 200:** "The probe's 219 names:" → "The probe's 227 names:". At the end of that paragraph (line 203, after "the layout facts"), add "; and #118's round 3: `Action.apply_state`/`_inputPos`/`_workTapePos`/`_output`, `MultiTapeTM.step_of_some`, `MultiTapeTM.outputSymbol_of_some`, `counterWord_succ`, `scanResult_keep_keep`".
- `audits/evidence/drafts/b6-fill-rulerdevice.DRAFT.md`:
  - **Line 93:** "(`B6F5ImportProbe.lean.txt`, 52 `#check`s)" → "(`B6F5ImportProbe.lean.txt`, 58 `#check`s; re-run against `oleans-lbapi4`; 52 before round 3)".
  - **Line 47** ("against the olean snapshot of #118's replays (`oleans-lbapi2`)"): append "; the import probe's round-3 re-run is against `oleans-lbapi4`".
  - **Line 170:** "The probe's 52 names, in seven groups:" → "The probe's 58 names, in eight groups:". After line 177 ("the renamings' field equations (#118's round 2)."), add "- the live-step API (#118's round 3): `Action.apply_*`, `MultiTapeTM.step_of_some`, `outputSymbol_of_some`." Line 177's final period becomes a semicolon.
- `audits/evidence/drafts/README.md`:
  - **Line 10** (the `b6-fill-rulerdevice` row): "52 names" → "58 names".
  - Line 15's "Pre-ship, all against `oleans-lbapi2`" stays historical. Optionally add "(F5's and MIG-12's probes re-run at round 3 against `oleans-lbapi4`: 58 and 227)".
- The "52" in the MIG-12 draft at lines 79, 194 and 260 is CfgRecord's 52-module closure, not a probe count: no change.

The pack and resolutions already say 227 and 58.
