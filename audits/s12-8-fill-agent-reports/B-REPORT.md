# §12.8 stream B fill report

**Result: 4/4 audited contracts proved.** No remaining `sorry` in `Scan.lean`, no sorried private helper, and no target proved modulo a helper.

## Delivery and base

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch checked out: `complexity/arora-barak-ch3-4`.
- Base: `37ab609199b2fad253b136375243db20faf88b16`.
- `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD`: exit 0 before editing.
- Work branch: `fill/s128-B`; no rebase, push, or PR.
- Delivery commit: `bda5a46f8a21a7343ed5c208f63d3e91077083f3`. The single patch and bundle are against the recorded base; the bundle requires that base commit and verifies successfully.
- Only changed repository file: `TCSlib/Complexity/TuringMachine/Build/Scan.lean`.

## Final verification result

- Required 74-module final sweep: **PASS**, zero errors, **33** sorry warnings, exactly the expected out-of-scope set.
- `Build/Scan`: zero errors, zero sorry warnings; all four contracts proved without `sorryAx`.
- Downstream: `Build/CounterLoop` 1; `Build/InputCall` 2; `Build/CfgRecord` 5; `ClassPSPACE/TQBF` 4; `ClassPSPACE` and `TuringMachine` facades 0.
- Untouched upstream: `Build/Seam` 1; `Build/Catalog` 12; `NDCodes` 1; `Constructible` 2; `ConfigGraph` 3; `Inclusions` 2. All other checked modules have 0.
- Campaign lint: **0 FAIL**; both duplication screens satisfy the brief.

The full sweep is `final-sweep.log`; per-module sorry counts are `evidence/final-counts.json`. The bootstrap had the expected 37, and the final sweep removes exactly this stream's four warnings. Final sweep tail:

```text
CHECK TCSlib/Complexity/ClassPSPACE/Games
PASS TCSlib/Complexity/ClassPSPACE/Games sorry=0
CHECK TCSlib/Complexity/ClassPSPACE
PASS TCSlib/Complexity/ClassPSPACE sorry=0
CHECK TCSlib/Complexity/TuringMachine/NDCodes
TCSlib/Complexity/TuringMachine/NDCodes.lean:179:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/NDCodes sorry=1
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
PASS TCSlib/Complexity/TuringMachine/Robustness/Bidirectional sorry=0
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine sorry=0
FINAL SWEEP PASS: modules=74, errors=0, sorry_warnings=33
```

## Proof routes

| Contract | Route | Forward family | Return family | Exit |
|---|---|---|---|---|
| `writeConstTM_run_ofCfg` | `scan_const_trace` applies public `catalog_trace_run`, length `w₀.length` | `scanConstF`: written prefix, `.wr` counter | `scanConstR`: full written word, `.bk` counter, head offset `r` | `scanConstD`: `.done`, full overwrite, restored heads |
| `writeAdvTM_run_ofCfg` | `scan_adv_run`: one forward induction through `w₀.length`, then one stationary step | `scanAdvF`: written prefix, state equal to written-cell count | none | state `0`, head advanced by `w₀.length` |
| `inputCopyTM_run_ofCfg` | `scan_copy_trace` applies public `catalog_trace_run`, length `x.length` | `scanCopyF`: shared prefix, `.sweep`, input at `r+1` | `scanCopyR`: full copy, `.rewind`, input at `r`, work offset `r−1` | `scanCopyD`: `.done`, full copy, both heads restored |
| `inputFoldTM_run_ofCfg` | `scan_fold_trace` applies public `catalog_trace_run`, length `x.length` | `scanFoldF`: fold of `x.take r`, input at `r+1` | `scanFoldR`: full fold, input at `r` | literal `{ d with state := some (.done (x.foldl δ a₀)) }` |

All finite-state indices and native-input positions use `min` to make the families total. The constant-writer and copier exit definitions use their forward family's final tape map, definitionally equal to the target's finish.

The advancing writer is cyclic. Its exit `0` is also its entry; for a nonempty word the next step writes again. Thus the stationary-exit hypothesis of `catalog_trace_run` is unavailable, and the single forward induction is necessary. No other induction was introduced.

The three writing rows share `scanWriteCfg` and `scan_write_step`. The latter cites `step_of_tapeAction_write`, and its sole written-cell argument cites `catalog_write_take`. None of the three consumers proves a one-cell overwrite again.

| Routine | Forward | Turn | Return | Entry | Exit stationarity |
|---|---|---|---|---|---|
| Constant writer | `scan_write_step` | `step_of_inputMoveAction` | `step_of_tapeAction_move` | `step_of_inputMoveAction` | `step_of_inputMoveAction` |
| Advancing writer | `scan_write_step` | final `step_of_inputMoveAction` returning to `0` | — | — | not asserted |
| Input copy | `scan_write_step` | `step_of_tapeAction_move` | `step_of_tapeAction_move` | `step_of_tapeAction_move` | `step_of_inputMoveAction` |
| Input fold | `step_of_inputMoveAction` | `step_of_inputMoveAction` | `step_of_inputMoveAction` | `step_of_inputMoveAction` | `step_of_inputMoveAction` |

Input reads cite generic `inputSymbolInner` or compute an end-marker read from `Cfg.inputSymbol`. Input movement cites `moveInputPos_zero`, `moveInputPos_pos_of_ne_right`, or `FinTM.moveInputPos_neg_val`. The fold's accumulator step uses `List.take_succ`, `List.getElem?_eq_getElem`, and `List.foldl_append`.

The final clauses are consequences of the instantiated public trace (or the bounded forward run): exact finish, no early exit, and every head's trajectory. The proof covers empty words/input, arbitrary nonblank frames, negative head coordinates, arbitrary alphabets, and zero work tapes for the fold. The copier's return is guided only by the input; the fold fixes every work head throughout.

## New private declarations

| Declaration | Role |
|---|---|
| `scanWriteCfg` | Shared framed partial overwrite and advancing head |
| `scan_write_step` | Shared machine-step equation, citing both public writing lemmas |
| `scanConstF` | Constant writer's forward family |
| `scanConstR` | Constant writer's return family |
| `scanConstD` | Constant writer's finish |
| `scan_const_trace` | Constant writer's public trace instance |
| `scanAdvF` | Advancing writer's forward family |
| `scan_adv_run` | The sole forward time induction |
| `scanCopyF` | Input copier's forward family |
| `scanCopyR` | Input copier's return family |
| `scanCopyD` | Input copier's finish |
| `scan_copy_trace` | Input copier's public trace instance |
| `scanFoldF` | Input fold's forward family |
| `scanFoldR` | Input fold's return family |
| `scan_fold_trace` | Input fold's public trace instance |

Every new declaration is private and documented. Nontrivial helpers carry a proof sketch. New exports: none. Requested shared lemmas: none. Imports: unchanged. Escalations: none.

## Frozen surface and permitted prose edits

The four theorem statements, five complete landed definitions (including `WritePhase`), all public docstrings, and the single import are byte-identical to the base. Public declaration names, kinds, and order remain unchanged. No declarations were removed.

Flagged status-only edits: (1) the module's **Status: statements.** paragraph now says **Status: proved.** and describes the three trace instances and advancing induction; (2) Main results' `(statements)` tag becomes `(proved)`. No sketch appendix was added.

## Environment and verification

Lean is the pinned `leanprover/lean4:v4.25.0`; mathlib is `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Dependency setup used `lake exe cache get` for the direct Mathlib imports of the prescribed closure; the targeted cache request completed successfully. Every Lean elaboration check used the unchanged `scripts/lean_check_tree.sh`. `lake build` was never run.

The prescribed 74-module bootstrap encountered one process-level `Bus error` (exit 135) in unchanged `CodeFormat.lean` while a cache refresh was active, without an elaboration diagnostic. Compiled dependency files were isolated from other local work, and the same module then passed without source changes; the bootstrap continued in order. The final sweep is the authoritative complete verification log.

This environment needs a narrow startup compatibility shim: Lean's `/proc/<its-pid>/exe` lookup is redirected to `/proc/self/exe`, with all other `readlink` calls unchanged. Its source is included as `evidence/lean-self-path.c`. It does not modify Lean, the proof checker, or diagnostics. A normal Lean installation should not need it. To reproduce here, compile it with `cc -shared -fPIC evidence/lean-self-path.c -ldl -o /tmp/s128-lean-self-path.so` and set `LD_PRELOAD` to that absolute path while running the campaign script.

## Duplication governance

Both prescribed populations were screened before and after. The screened base files are byte-identical to `5afed90b`; the primary baseline is 550 declarations / 415 directed pairs / 121,938 characters, and the advisory baseline is 283 / 230 / 71,309.

The only allowed new cross-file pair is `scanWriteCfg` ↔ `catalogCopyF`: these are framed configuration definitions for different machines, not a duplicated proof (55–56%). No other new cross-file pair is permitted or introduced.

**new copies: none**. There is one cited two-pass trace, one shared writing step citing the public interval-write fact, and one forward induction for the cyclic row; no Catalog or EmitIterBody private proof was copied or re-derived.

## File size

| File | Base lines | Final lines | Base bytes | Final bytes |
|---|---:|---:|---:|---:|
| `TCSlib/Complexity/TuringMachine/Build/Scan.lean` | 276 | 666 | 13,684 | 31,874 |

No new repository files or source modules were added. The file stays below the 1,000-line split threshold; its 666 lines contain the four owned routines and their shared write family. The final source's SHA-256 is `87b78236eb7ae51c20b9a4f8b6229c802932febf3841226f66fd2de97e88f79d`.

## Axioms and lint

The four axiom prints were obtained by temporarily appending `#print axioms` commands to the owned module and checking it through `scripts/lean_check_tree.sh`. The commands were then removed before the delivery commit; the final sweep checks the uninstrumented source. The results are:

```text
'Turing.writeConstTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.writeAdvTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.inputCopyTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.inputFoldTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Scan.lean` has zero errors and zero sorry warnings. Lean reports nine non-admission `linter.unnecessarySeqFocus` suggestions; no linter is disabled. The complete axiom-check output is `axioms.log`.

```text
style_lint: 0 FAIL, 6 WARN over 16 files
```

The six campaign style warnings are unchanged from the base and concern out-of-scope files. Full output: `evidence/lint.txt`.

## New in-file screen pairs

The same four new directed pairs occur in both populations:

| Target reproduces source | Fraction | Justification |
|---|---:|---|
| `writeConstTM_run_ofCfg` → `inputCopyTM_run_ofCfg` | 265/412 = 64% | Both extract exact finish, first exit and head bounds from their own trace instance; the machine-specific families and trajectory intervals differ. |
| `inputCopyTM_run_ofCfg` → `writeConstTM_run_ofCfg` | 265/422 = 63% | Reverse direction of the preceding clause-extraction similarity; no transition or trace induction is duplicated. |
| `inputCopyTM_run_ofCfg` → `inputFoldTM_run_ofCfg` | 202/321 = 63% | Both split the public trace's phases to obtain contract clauses; the fold preserves every work head, while the copier uses its moving-head interval. |
| `scan_const_trace` → `scan_adv_run` | 247/476 = 52% | Both initialize the same shared write family and discharge finite-index bookkeeping around `scan_write_step`; one instantiates the two-pass trace, while the other contains the expressly required sole forward induction. |

No new in-file pair reaches 90%. The pre-existing 58% `writeConstTM` → `writeAdvTM` table pair is unchanged.

## Screen summaries

| Population | Before: declarations / pairs / matched characters | After: declarations / pairs / matched characters |
|---|---|---|
| Prescribed main population | 550 / 415 / 121,938 | 566 / 421 / 123,143 |
| Advisory population | 283 / 230 / 71,309 | 299 / 234 / 72,288 |

The main screen adds six directed pairs (the four in-file pairs and the allowed cross-file pair in both directions); the advisory screen adds only the four in-file pairs. No pair disappears. Diffs are included in `evidence/screen-diff.txt` and `evidence/advisory-diff.txt`.

### Main screen — before

```text
declarations screened: 550; copy pairs (target reproduces >= half of source): 415; reproduced text: 121,938 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
```

### Main screen — after

```text
declarations screened: 566; copy pairs (target reproduces >= half of source): 421; reproduced text: 123,143 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::catalogCopyF  reproduces  Scan.lean::scanWriteCfg: 113/202 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Scan.lean::scanWriteCfg  reproduces  Catalog.lean::catalogCopyF: 113/206 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
```

### Advisory screen — before

```text
declarations screened: 283; copy pairs (target reproduces >= half of source): 230; reproduced text: 71,309 chars
   Simulation.lean::timed_rewind  reproduces  Primitives.lean::catalogRewind: 435/435 = 100%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Primitives.lean::emitterSplit_find  reproduces  Primitives.lean::splitFind_eq: 227/228 = 100%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::emitterToken_separator: 215/217 = 99%
   EmitIterBody.lean::control_step'  reproduces  EmitIterBody.lean::control_step: 164/166 = 99%
   Primitives.lean::emitterP2SmallIndex  reproduces  Primitives.lean::emitterP2PairIndex: 207/212 = 98%
   EmitIterBody.lean::rwTape_some  reproduces  EmitIterBody.lean::rwTape_none: 1015/1042 = 97%
   Primitives.lean::scanTrues_run  reproduces  Primitives.lean::scanStep_right: 153/158 = 97%
   Primitives.lean::emitterP2_right_frame  reproduces  Primitives.lean::emitterP2_left_frame: 273/282 = 97%
   Primitives.lean::splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 227/235 = 97%
   Primitives.lean::emitterP2_left_frame  reproduces  Primitives.lean::emitterP2_right_frame: 273/283 = 96%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairConcat: 147/153 = 96%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Primitives.lean::emitterP2_body_erase_right  reproduces  Primitives.lean::emitterP2_body_erase_left: 1078/1127 = 96%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 827/866 = 95%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 827/866 = 95%
   Primitives.lean::emitterP2_body_erase_left  reproduces  Primitives.lean::emitterP2_body_erase_right: 1078/1134 = 95%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairFst: 147/155 = 95%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::scanStep_right: 148/158 = 94%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_separator: 201/217 = 93%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_small_frame: 539/582 = 93%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_pair_frame: 539/583 = 92%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanStep_right: 146/158 = 92%
   EmitIterBody.lean::rwTape_none  reproduces  EmitIterBody.lean::rwTape_some: 1015/1108 = 92%
   Primitives.lean::emitterP2PairIndex  reproduces  Primitives.lean::emitterP2SmallIndex: 207/226 = 92%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanStep_right: 143/158 = 91%
   Primitives.lean::mapParse_block  reproduces  Primitives.lean::mapParse_first: 244/271 = 90%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 276/308 = 90%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Primitives.lean::emitter_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_update_left: 542/633 = 86%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_control: 71/83 = 86%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_run: 408/482 = 85%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_update_right: 542/648 = 84%
   Primitives.lean::emitterSplit_result  reproduces  Primitives.lean::splitLoop_result: 193/231 = 84%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 630/755 = 83%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairConcat: 125/153 = 82%
   Primitives.lean::catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   EmitIterBody.lean::embed_ofWords_right  reproduces  EmitIterBody.lean::embed_ofWords_left: 103/127 = 81%
   EmitIterBody.lean::embed_ofWords_left  reproduces  EmitIterBody.lean::embed_ofWords_right: 103/127 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Primitives.lean::splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_prepare_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_erase_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairSnd: 125/155 = 81%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 630/790 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::extract_first: 226/285 = 79%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 505/639 = 79%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanStep_right: 122/158 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 408/533 = 77%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 408/537 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairFst: 117/155 = 75%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairSnd: 117/155 = 75%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::extract_replay_finish: 224/298 = 75%
   Primitives.lean::splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 672/896 = 75%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 338/451 = 75%
   EmitIterBody.lean::copyCfg  reproduces  EmitIterBody.lean::fullCfg: 71/95 = 75%
   Primitives.lean::emitterP2_body_length  reproduces  Primitives.lean::emitterP2_body_width: 493/665 = 74%
   EmitIterBody.lean::rwInput_zero  reproduces  EmitIterBody.lean::rwInput_some: 547/739 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Primitives.lean::extract_block  reproduces  Primitives.lean::extract_first: 210/285 = 74%
   Primitives.lean::splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Primitives.lean::emitterP2_body_width  reproduces  Primitives.lean::emitterP2_body_length: 493/674 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Primitives.lean::mapStart  reproduces  Primitives.lean::lenStart: 1210/1659 = 73%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 366/506 = 72%
   Primitives.lean::splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 326/451 = 72%
   Primitives.lean::splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::emitterSplit_of_body  reproduces  Primitives.lean::splitSolve_of_body: 672/940 = 71%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   EmitIterBody.lean::control_step  reproduces  EmitIterBody.lean::control_step': 164/232 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 209/298 = 70%
   Primitives.lean::splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_double: 543/785 = 69%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Primitives.lean::emitterTokenTM  reproduces  Primitives.lean::pairDupTM: 266/386 = 69%
   Primitives.lean::emitterP2_erase_run  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_right_frame: 192/283 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 356/533 = 67%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_right_frame: 189/283 = 67%
   Primitives.lean::emitterP2_body_prepare  reproduces  Primitives.lean::emitterP2_body_compare: 566/849 = 67%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 270/406 = 67%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::emitterTokenTM: 266/400 = 66%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_left_frame: 186/282 = 66%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Primitives.lean::extract_run  reproduces  Primitives.lean::lenParse_run: 1077/1643 = 66%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Primitives.lean::lenStart  reproduces  Primitives.lean::mapStart: 1210/1864 = 65%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_left_frame: 183/282 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   EmitIterBody.lean::rwInput_some  reproduces  EmitIterBody.lean::rwInput_zero: 547/848 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 321/499 = 64%
   Primitives.lean::splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_setup: 366/571 = 64%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::emitterP2_body_compare  reproduces  Primitives.lean::emitterP2_body_prepare: 566/894 = 63%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanCopy_run: 305/482 = 63%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitPrepare_rewind: 477/755 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitPrepare_rewind: 476/755 = 63%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Primitives.lean::lenCfg  reproduces  Primitives.lean::mapCfg: 99/160 = 62%
   Primitives.lean::pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   Primitives.lean::lenParse_block  reproduces  Primitives.lean::lenParse_first: 189/308 = 61%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 505/831 = 61%
   EmitIterBody.lean::fullCfg  reproduces  EmitIterBody.lean::copyCfg: 71/117 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Primitives.lean::mapBuffer_rewind  reproduces  Primitives.lean::mapPayload_replay: 372/617 = 60%
   Primitives.lean::mapParse_first  reproduces  Primitives.lean::mapParse_block: 244/405 = 60%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::rawStrip_erase: 213/354 = 60%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanCopy_finish: 154/257 = 60%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Primitives.lean::emitter_compare_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 189/316 = 60%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 382/639 = 60%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::splitBody_rewind: 321/538 = 60%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitRestore_rewind: 467/790 = 59%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitRestore_rewind: 466/790 = 59%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::extract_run: 1077/1854 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/217 = 58%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   EmitIterBody.lean::copy_step  reproduces  EmitIterBody.lean::copy_end: 487/861 = 57%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 427/755 = 57%
   Primitives.lean::emitterP2_prepare_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 178/316 = 56%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/217 = 56%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Primitives.lean::mapCfg  reproduces  Primitives.lean::lenCfg: 99/177 = 56%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::scanStep_right: 88/158 = 56%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::pairDup_double: 653/1176 = 56%
   Primitives.lean::emitterP2_erase_scan  reproduces  Primitives.lean::rawStrip_replay: 225/406 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 175/316 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 479/866 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 479/866 = 55%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanCopy_finish: 142/257 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::emitterTokenTM: 220/400 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Primitives.lean::catalogRewind: 239/435 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::splitPrepare_rewind: 414/755 = 55%
   Primitives.lean::emitter_compare_run  reproduces  Primitives.lean::emitterP2_erase_scan: 173/316 = 55%
   Primitives.lean::extract_run  reproduces  Primitives.lean::pairValid_run: 641/1177 = 54%
   Simulation.lean::bufferTape_append  reproduces  Primitives.lean::catalogBuffer_erase: 64/118 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 469/866 = 54%
   Primitives.lean::pairValid_computes  reproduces  Primitives.lean::anyTrue_computes: 137/253 = 54%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::splitBody_restore: 270/499 = 54%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Primitives.lean::splitPoly_loop_end: 380/703 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 468/866 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitEmit_separator: 411/765 = 54%
   EmitIterBody.lean::FinTM.exists_emitIterTM  reproduces  Primitives.lean::emitter_width_budget: 69/129 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_scan: 338/639 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::scanStep_right: 83/158 = 53%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_finish: 135/257 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::pairValid_run  reproduces  Primitives.lean::anyTrue_run: 413/795 = 52%
   Primitives.lean::rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::rawStrip_rewind: 362/704 = 51%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::scanCopy_suffix: 437/850 = 51%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::pairValid_run: 605/1177 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Primitives.lean::mapPayload_replay  reproduces  Primitives.lean::rawStrip_replay: 208/406 = 51%
   Primitives.lean::splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitter_compare_scan: 334/654 = 51%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/355 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 400/790 = 51%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_extra: 228/451 = 51%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_double: 396/785 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::rawStrip_replay: 204/406 = 50%
   EmitIterBody.lean::copy_end  reproduces  EmitIterBody.lean::copy_step: 487/974 = 50%
   Primitives.lean::extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
```

### Advisory screen — after

```text
declarations screened: 299; copy pairs (target reproduces >= half of source): 234; reproduced text: 72,288 chars
   Simulation.lean::timed_rewind  reproduces  Primitives.lean::catalogRewind: 435/435 = 100%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Primitives.lean::emitterSplit_find  reproduces  Primitives.lean::splitFind_eq: 227/228 = 100%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::emitterToken_separator: 215/217 = 99%
   EmitIterBody.lean::control_step'  reproduces  EmitIterBody.lean::control_step: 164/166 = 99%
   Primitives.lean::emitterP2SmallIndex  reproduces  Primitives.lean::emitterP2PairIndex: 207/212 = 98%
   EmitIterBody.lean::rwTape_some  reproduces  EmitIterBody.lean::rwTape_none: 1015/1042 = 97%
   Primitives.lean::scanTrues_run  reproduces  Primitives.lean::scanStep_right: 153/158 = 97%
   Primitives.lean::emitterP2_right_frame  reproduces  Primitives.lean::emitterP2_left_frame: 273/282 = 97%
   Primitives.lean::splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 227/235 = 97%
   Primitives.lean::emitterP2_left_frame  reproduces  Primitives.lean::emitterP2_right_frame: 273/283 = 96%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairConcat: 147/153 = 96%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Primitives.lean::emitterP2_body_erase_right  reproduces  Primitives.lean::emitterP2_body_erase_left: 1078/1127 = 96%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 827/866 = 95%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 827/866 = 95%
   Primitives.lean::emitterP2_body_erase_left  reproduces  Primitives.lean::emitterP2_body_erase_right: 1078/1134 = 95%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairFst: 147/155 = 95%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::scanStep_right: 148/158 = 94%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_separator: 201/217 = 93%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_small_frame: 539/582 = 93%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_pair_frame: 539/583 = 92%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanStep_right: 146/158 = 92%
   EmitIterBody.lean::rwTape_none  reproduces  EmitIterBody.lean::rwTape_some: 1015/1108 = 92%
   Primitives.lean::emitterP2PairIndex  reproduces  Primitives.lean::emitterP2SmallIndex: 207/226 = 92%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanStep_right: 143/158 = 91%
   Primitives.lean::mapParse_block  reproduces  Primitives.lean::mapParse_first: 244/271 = 90%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 276/308 = 90%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Primitives.lean::emitter_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_update_left: 542/633 = 86%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_control: 71/83 = 86%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_run: 408/482 = 85%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_update_right: 542/648 = 84%
   Primitives.lean::emitterSplit_result  reproduces  Primitives.lean::splitLoop_result: 193/231 = 84%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 630/755 = 83%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairConcat: 125/153 = 82%
   Primitives.lean::catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   EmitIterBody.lean::embed_ofWords_right  reproduces  EmitIterBody.lean::embed_ofWords_left: 103/127 = 81%
   EmitIterBody.lean::embed_ofWords_left  reproduces  EmitIterBody.lean::embed_ofWords_right: 103/127 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Primitives.lean::splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_prepare_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_erase_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairSnd: 125/155 = 81%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 630/790 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::extract_first: 226/285 = 79%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 505/639 = 79%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanStep_right: 122/158 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 408/533 = 77%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 408/537 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairFst: 117/155 = 75%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairSnd: 117/155 = 75%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::extract_replay_finish: 224/298 = 75%
   Primitives.lean::splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 672/896 = 75%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 338/451 = 75%
   EmitIterBody.lean::copyCfg  reproduces  EmitIterBody.lean::fullCfg: 71/95 = 75%
   Primitives.lean::emitterP2_body_length  reproduces  Primitives.lean::emitterP2_body_width: 493/665 = 74%
   EmitIterBody.lean::rwInput_zero  reproduces  EmitIterBody.lean::rwInput_some: 547/739 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Primitives.lean::extract_block  reproduces  Primitives.lean::extract_first: 210/285 = 74%
   Primitives.lean::splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Primitives.lean::emitterP2_body_width  reproduces  Primitives.lean::emitterP2_body_length: 493/674 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Primitives.lean::mapStart  reproduces  Primitives.lean::lenStart: 1210/1659 = 73%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 366/506 = 72%
   Primitives.lean::splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 326/451 = 72%
   Primitives.lean::splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::emitterSplit_of_body  reproduces  Primitives.lean::splitSolve_of_body: 672/940 = 71%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   EmitIterBody.lean::control_step  reproduces  EmitIterBody.lean::control_step': 164/232 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 209/298 = 70%
   Primitives.lean::splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_double: 543/785 = 69%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Primitives.lean::emitterTokenTM  reproduces  Primitives.lean::pairDupTM: 266/386 = 69%
   Primitives.lean::emitterP2_erase_run  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_right_frame: 192/283 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 356/533 = 67%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_right_frame: 189/283 = 67%
   Primitives.lean::emitterP2_body_prepare  reproduces  Primitives.lean::emitterP2_body_compare: 566/849 = 67%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 270/406 = 67%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::emitterTokenTM: 266/400 = 66%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_left_frame: 186/282 = 66%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Primitives.lean::extract_run  reproduces  Primitives.lean::lenParse_run: 1077/1643 = 66%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Primitives.lean::lenStart  reproduces  Primitives.lean::mapStart: 1210/1864 = 65%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_left_frame: 183/282 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   EmitIterBody.lean::rwInput_some  reproduces  EmitIterBody.lean::rwInput_zero: 547/848 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 321/499 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Primitives.lean::splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_setup: 366/571 = 64%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::emitterP2_body_compare  reproduces  Primitives.lean::emitterP2_body_prepare: 566/894 = 63%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanCopy_run: 305/482 = 63%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitPrepare_rewind: 477/755 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitPrepare_rewind: 476/755 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Primitives.lean::lenCfg  reproduces  Primitives.lean::mapCfg: 99/160 = 62%
   Primitives.lean::pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   Primitives.lean::lenParse_block  reproduces  Primitives.lean::lenParse_first: 189/308 = 61%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 505/831 = 61%
   EmitIterBody.lean::fullCfg  reproduces  EmitIterBody.lean::copyCfg: 71/117 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Primitives.lean::mapBuffer_rewind  reproduces  Primitives.lean::mapPayload_replay: 372/617 = 60%
   Primitives.lean::mapParse_first  reproduces  Primitives.lean::mapParse_block: 244/405 = 60%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::rawStrip_erase: 213/354 = 60%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanCopy_finish: 154/257 = 60%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Primitives.lean::emitter_compare_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 189/316 = 60%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 382/639 = 60%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::splitBody_rewind: 321/538 = 60%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitRestore_rewind: 467/790 = 59%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitRestore_rewind: 466/790 = 59%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::extract_run: 1077/1854 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/217 = 58%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   EmitIterBody.lean::copy_step  reproduces  EmitIterBody.lean::copy_end: 487/861 = 57%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 427/755 = 57%
   Primitives.lean::emitterP2_prepare_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 178/316 = 56%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/217 = 56%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Primitives.lean::mapCfg  reproduces  Primitives.lean::lenCfg: 99/177 = 56%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::scanStep_right: 88/158 = 56%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::pairDup_double: 653/1176 = 56%
   Primitives.lean::emitterP2_erase_scan  reproduces  Primitives.lean::rawStrip_replay: 225/406 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 175/316 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 479/866 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 479/866 = 55%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanCopy_finish: 142/257 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::emitterTokenTM: 220/400 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Primitives.lean::catalogRewind: 239/435 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::splitPrepare_rewind: 414/755 = 55%
   Primitives.lean::emitter_compare_run  reproduces  Primitives.lean::emitterP2_erase_scan: 173/316 = 55%
   Primitives.lean::extract_run  reproduces  Primitives.lean::pairValid_run: 641/1177 = 54%
   Simulation.lean::bufferTape_append  reproduces  Primitives.lean::catalogBuffer_erase: 64/118 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 469/866 = 54%
   Primitives.lean::pairValid_computes  reproduces  Primitives.lean::anyTrue_computes: 137/253 = 54%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::splitBody_restore: 270/499 = 54%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Primitives.lean::splitPoly_loop_end: 380/703 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 468/866 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitEmit_separator: 411/765 = 54%
   EmitIterBody.lean::FinTM.exists_emitIterTM  reproduces  Primitives.lean::emitter_width_budget: 69/129 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_scan: 338/639 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::scanStep_right: 83/158 = 53%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_finish: 135/257 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::pairValid_run  reproduces  Primitives.lean::anyTrue_run: 413/795 = 52%
   Primitives.lean::rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::rawStrip_rewind: 362/704 = 51%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::scanCopy_suffix: 437/850 = 51%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::pairValid_run: 605/1177 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Primitives.lean::mapPayload_replay  reproduces  Primitives.lean::rawStrip_replay: 208/406 = 51%
   Primitives.lean::splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitter_compare_scan: 334/654 = 51%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/355 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 400/790 = 51%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_extra: 228/451 = 51%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_double: 396/785 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::rawStrip_replay: 204/406 = 50%
   EmitIterBody.lean::copy_end  reproduces  EmitIterBody.lean::copy_step: 487/974 = 50%
   Primitives.lean::extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
```

## Reuse and archive contents

Apply the single patch with `git am patches/0001-Prove-section-12.8-writers-and-native-input-sweeps.patch` on the recorded base. Alternatively, fetch the work branch from `fill-s128-B.bundle`; the bundle has the recorded base as its prerequisite. `evidence/bundle-verify.txt` records successful verification.

The archive contains this report, the complete modified source at its repository path, the format-patch series, the git bundle, the full final sweep, the axiom log, the screen/freeze/lint/environment evidence, and `SHA256SUMS`. The checksums cover every other archive file. No PR was opened and nothing was pushed.
