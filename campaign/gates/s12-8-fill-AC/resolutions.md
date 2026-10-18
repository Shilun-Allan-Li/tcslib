# §12.8 fill gate, streams A–C (24 targets): resolutions (CLOSED, round 1)

## Round 1 (2026-10-12): 0 blockers, 0 majors, 4 minors, 28 notes

The findings are verbatim in `audits/s12-8-fill-AC-findings.md`. The pack is
`audits/s12-8-fill-AC-pack.md`, with its 99-file bundle `audits/s12-8-fill-AC-bundle.md`. The
auditor found all 24 targets proved as the routes prescribe. It confirmed:
- the public freeze, by reverse-applying the cumulative patch to the five bases (note 6);
- the layout, scan, compare, seek and seam contracts and their sharing: one trace per family,
  with no duplicated run trace (notes 7–13);
- the frozen carrier's meaning, `cfgRecord_inj` and `recordValid_iff` (notes 14–15);
- the record step's single phase host, its single R1 restriction with dedicated digit banks,
  the binary save and exact restore of the native position, and the clamps (notes 18–21);
- outward moves rejected before any record rewrite, the exact field-by-field rewrite, global
  scratch cleanup, and the coefficient `200·(k + 3)·(Cseek + 1)` (notes 21–23);
- the halted-source, empty-input, displaced-frame and nontermination cases (note 24);
- the input seek and the time-only clean call (note 26);
- exit interception (note 27).

On the pack's question 6 it ruled that **no pair in the clear-phase family must be factored**
(note 28). A generic in-file clear-and-dispatch wrapper is an optional cleanup, not debt.

| Finding | Disposition |
|---|---|
| 1 (minor): the supplied union screen is not of the final population; the replay descriptions conflate revisions; "outside A–C's closure" needs qualification | **Resolved, records only.** The union screen rerun at the final head is `audits/evidence/s12-8/fill-gate/screen-union-final.txt`: **1,202 declarations, 1,412 pairs, 547,045 characters**, exactly the auditor's figures. Its difference from the supplied screen lies entirely in `TQBF.lean`, filled afterwards by B4a, and adds no pair involving an A–C file. The supplied `screen-union-head.txt` is kept as issued. **The replay stages, by revision:** the combined replay `audits/logs/fills-4-replay.log` at `b0e922ab` (11 modules); the top-up `fills-4-replay-topup.log` at `b13425cb` (15); and the second top-up `fills-4-replay-topup2.log` at `7b3c4747` (2). All three have 0 errors. **Correction:** the files changed in the two top-ups lie outside A–C's **owned files**, not outside its downstream closure. `TQBF` imports `CfgRecord`, and the record tables build on the record layer. Neither top-up changed an A–C file |
| 2 (minor): the pack's claim that no delivery introduced a cross-file pair involving its owned files is false | **Corrected, records only.** Three directed screen matches involve A–C files. (a) `Catalog.lean::catalogCopyF` ↔ `Scan.lean::scanWriteCfg`, 113/202 and 113/206 (56%, 55%). Stream B's brief authorizes this framed-configuration similarity, and B's report discloses it. (b) `EmitIterBody.lean::emitIterBody` → `InputCall.lean::inputSeekRewind`, 145/257 (56%). This is the short native-rewind transition scaffold. The exit convention differs, and `inputSeekRewind_run` cites the public `FinTM.rewind_heads` rather than copying a rewind proof. All three are **term-level matches, not copied proved material**, so no debt arises and no refactor is needed. No pair involves `CfgRecord`. The pack's blanket sentence is superseded by this entry, and the pack is kept unchanged under the archival rule |
| 3 (minor): the hand-table count is five, not three | **Corrected, records only.** Stream C adds **three hand tables in record stepping** (`recordStepProbe`, `recordStepSave`, `recordStepRead`, over `inputMoveAction`) **plus the two input-seek tables** (`inputSeekRewind`, `inputSeekStep`). C's original brief rule 10 authorizes all five, and each carries the missing-native-primitive explanation. `inputSeekRewind` uses `FinTM.controlAction` to meet the public rewind theorem's hypotheses, and that exception stands. The public native-input-head primitive remains a 12.2c candidate |
| 4 (minor): stale current-tense descriptions in `InputCall` and in `recordStepRows` | **Fixed, comment-only.** In `InputCall.lean`, the module Status and the Main-results entry for `exists_inputCallTM` now read "proved", with the copier `inputCopyTM_run_ofCfg` named as a proved dependency, and `inputCall_copy`'s docstring no longer calls it admitted. In `CfgRecord.lean`, `recordStepRows` now says "No lifted Bool row selects the record tape; the rich scans and copies do select tape 0." The historical continuation appendices are kept. The comment-stripped code of both files is identical to the audited files, and both elaborate read-only with 0 errors and 0 warnings (`audits/logs/s12-8-fill-AC-close.log`) |
| 5–32 (notes) | Confirmed. Note 6: inventory counts are of named declarations; CfgRecord also has seven private instances. Note 21: "before anything is written" means before any record rewrite. Note 27: consumers must intercept a verdict before another underlying-row step, as the statement gate required; no all-time bound is certified. Notes 31–32: replay, axiom, lint and delivery-history execution remain maintainer attestations, as the pack states |

**Gate CLOSED.** The 24 §12.8 rows of streams A–C are filled, admission-free and audited:
- stream A, the field layout, scans, compare, seeks and the two-exit seam (13);
- stream B, the four Scan contracts (4);
- stream C, the record rows, including R8.7 `exists_recordStepTM`, and the input calls (7).

With stream D's R8.0b gate, closed earlier, **§12.8 is complete.** The A–C files (`Catalog`,
`Seam`, `Scan`, `CfgRecord`, `InputCall`) leave gate custody. This unblocks the §13d G2–G4
statements (G2 lives in `Catalog`), the optional clear-and-dispatch wrapper, and the
native-input-head primitive.
