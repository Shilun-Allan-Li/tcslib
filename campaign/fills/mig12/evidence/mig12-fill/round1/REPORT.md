# MIG-12 CfgRecord fill report

**Partial delivery under ground rule 9.** The stopping point is the end of Phase 1. Phase 2 is pending; the original row proofs are retained. Resource pressure made additional whole-file verification expensive, so this delivery uses the explicitly permitted phase boundary. The file is admission-free. Every public statement and public docstring is unchanged.

The three public rows have the mechanical segment recomposition needed by Phase 1. Completion of Phase 3 over fully migrated phases is not claimed. Phase 4 resolves/removes **5 of 173** ledger sites; **168 remain explicitly pending** below. Phase proof bodies retain their prior local arguments, apart from the mechanical segment swap and the listed field-API corrections. No missing API obstruction was encountered in the delivered portion, and no ground rule was relaxed. The remaining work is deferred under the continuation rule, rather than represented as complete.

## Repository, first edit, and provenance

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Cloned campaign branch: `complexity/arora-barak-ch3-4`, observed at `c487ef9d1a353c53a9e57f560899e9e0a00720a5`.
- Base and sole bundle prerequisite: **`94b986d4db7167ab2a8b20d38d4385f11e60be0e`**.
- `git merge-base --is-ancestor 94b986d4db7167ab2a8b20d38d4385f11e60be0e HEAD` succeeded on the campaign branch before creation of `fill/mig12-cfgrecord` at that exact base. The setup evidence also repeats the ancestor check against the recorded campaign tip and includes the reflog.
- No rebase, merge, cherry-pick, push, or PR. Only `TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean` is changed in the commit series.
- The first edit and first commit, `61c25b247918bbccdc04e524a75c4836fbe1c4bd`, add only `import TCSlib.Complexity.TuringMachine.Build.Contract`. No other import is added or changed.
- Delivery head: `41d31d09e4c8ff9fd645bfa338fbc34e2a4b818d`.

| Input | Verified SHA-256 |
|---|---|
| Attached `mig12-fill-cfgrecord.md` | `d815282a8dc1549212569fdf93c3bc7b55552008b314e0e1408aaf081b02d247` |
| Attached environment addendum | `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928` |
| Exact authorized shim source | `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7` |

The repository brief matches the attachment byte for byte after replacing its three `@ANCESTOR@` placeholders with the base hash.

## Runtime and bootstrap

The pinned, unmodified toolchain initially failed with `error: failed to locate application`. The exact addendum source was compiled in scratch with `cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so`. With the authorized fallback, Lean reports version **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, Release. The toolchain was reused read-only; no permissions or toolchain files were changed and no sandbox escalation was requested.

These variables were set only for Lean/Lake commands and their checking scripts:

```text
PATH=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux/bin:$PATH
LEAN_SYSROOT=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/ae5a4f03be48/evidence/runtime/executable-path.so
```

For cache retrieval, `TAR_OPTIONS=--no-same-owner` resolved the initial leantar archive ownership error. The full 7,506-file cache request was canceled; a targeted `lake exe cache get` covered the Mathlib imports used by the prescribed order. A shared-cache `curl.cfg` race was resolved by setting `MATHLIB_CACHE_DIR=/workspace/scratch/ae5a4f03be48/evidence/runtime/mathlib-cache`. The successful retrieval decompressed 1,026 files. **No `lake build` was run.** The source is included at `evidence/runtime/executable-path.c`; no compiled shim, olean, or other build product is shipped.

The execution service disconnected during bootstrap module 134 (`Build/Catalog`) and final-sweep module 91 (`SpaceComplexity/Machines/Sim`). The checking processes disappeared, while files and completed logs survived. Both sweeps resumed at their interrupted module through the prescribed script, preserving completed checks and recording the interruption in the logs. No successful module was repeated for this recovery.

A second execution-service disconnect interrupted bootstrap module 186 (`SpaceComplexity/CounterProgSim`). The old session handles were closed, the unfinished module was resumed, and the waiting final-sweep/probe jobs were restarted. All 185 completed bootstrap checks and the source/evidence files were preserved.

The first bootstrap attempt at `CfgRecord` was killed with exit 137 and produced no olean. The shared memory limit was 8 GiB and its memory-event counter recorded one OOM kill. Overlapping final and candidate checks were stopped, the unused task-private compressed cache was removed, byte-identical already-checked oleans in the two own output trees were hardlinked to release duplicate storage, and Lean checks were serialized before retrying the failed module. The failed attempt remains in the bootstrap log.

During the slow replay, 880 byte-identical external dependency-cache oleans (379,015,032 bytes) were shared with the existing pinned runtime workspace. Both package HEADs matched the same manifest revisions, and each file was compared byte for byte before atomic replacement of this task's cache path. Nonmatching or unavailable entries were skipped. This changed cache storage only; all TCSlib checks still run through the prescribed fresh-output script. The resource log records the cache location and comparison-manifest hash.

The 279-module bootstrap used the import-only source and `scripts/lean_check_tree.sh`. Final checks use the same script and a separate output tree, with `TCSLIB_OLEANS=/workspace/scratch/ae5a4f03be48/evidence/work/final-oleans`. The final sweep began with unchanged upstream modules while bootstrap continued; a barrier before `CfgRecord` prevents it from checking the owned module before the source is ready. The initial Phase 1 candidate had four rewrite-matching errors at scalar boundaries. Explicit parameters alone did not fix them: the first final-sweep attempt reported the same four failures. The delivered source instead applies `recordSeg_iff.mp` directly to the composed segments. The failed attempt is retained in the final log, followed by the successful retry and downstream checks; the warning/error comparison uses each module's successful completed check. No downstream module was checked with the failing source. An earlier overlapping candidate retry was interrupted during resource recovery. No intermediate proof is admitted.

A later execution-service control-channel disconnect lost the session handles during the final replay. The processes initially survived and advanced through module 170, but subsequent inspection showed that they had exited and the handles could not be recovered. The unfinished module 171 (`CodeSimulator`), after-screen, and queued probes were restarted only after that confirmation. Completed checks, including the successful `CfgRecord` check, were preserved.

## Scope, declarations, and freeze

| Measure | Base | Delivery |
|---|---:|---:|
| Lines | 5,302 | 5310 |
| Public declarations, supplied freeze parser | 21 | 21 |
| Private declarations, supplied freeze parser | 98 | 98 |
| Admissions in owned source | 0 | 0 |

The supplied declaration freeze script reports no public additions, removals, or statement changes. An additional comparison checks every public statement prefix, including its docstring, byte for byte; all 21 match. The module header and namespace/section/open/variable commands are unchanged. The three obsolete `RecordRun`/`recordRun_trans` mentions left in the source are confined to frozen public docstrings. There is no executable reference to the retired definition or its helpers.

New private declarations:

| Declaration | Role |
|---|---|
| `RecordSeg` | The single allowed abbreviation, exactly the shared segment with two verdict states and the symmetric head box. |
| `record_headBox_iff` | Converts the published interval-box predicate to the frozen absolute-radius form. |
| `recordSeg_iff` | Reads `segment_iff`, set membership, and the box/radius equivalence at scalar interfaces; proves no run or composition law. |
| `record_headBox_mono` | Pure inclusion of radius boxes, supplied to `Segment.mono`. |
| `recordStep_tagged_segment` | Renamed and repointed prefix/dispatch packaging over `Segment`; consumes the host trajectory rather than retracing it. |

Deleted: `RecordRun`, `recordRun_zero`, `recordRun_trans`, `recordRun_mono`, and `recordRun_tagged`. Their replacements are itemized below.

Changed existing private declarations:

`record_tag_ne`, `recordStep_state_run`, `recordStep_phase_run`, `recordStep_read_prefix`, `recordStep_read_fields`, `recordStep_read_all`, `recordStep_halt_run`, `recordStep_empty_run`, `recordStep_reject_run`, `recordStep_prepare_native`, `recordStep_seek_read`, `recordStep_restore_digits`, `recordStep_restore_native`, `recordStep_live_native`, `recordStep_tape_run`, `recordStep_copyback_run`, `recordStep_write_back`, `recordStep_position_run`, `recordStep_apply_run`.

Their roles are given in the use and phase tables. `record_tag_ne` now reads `Cfg.mapState_state`; the host packaging reads `Cfg.mapState_workTapePos`. The other mechanical changes replace the segment representation and its operations. The only changed public bodies are `exists_recordStepTM`, `exists_recordEqTM`, and `exists_recordTestTM`, for the segment recomposition and conversion back to their frozen scalar conclusions.

Promotion candidates, kept private here: the symmetric `HeadBox` radius equivalence and inclusion. No public declaration is introduced.

## RecordRun retirement: every supplied inventory entry

| Base declaration | Replacement / disposition |
|---|---|
| `RecordRun` | Deleted; one private `RecordSeg` abbreviation of the specified `Segment` and symmetric `HeadBox`. |
| `recordStepMachine` | Inventory prose-only hit; machine definition unchanged. |
| `recordRun_mono` | Deleted; callers use `Segment.mono` and the head-box inclusion lemma. |
| `recordStepReadExit` | Inventory prose-only hit; exit definition unchanged. |
| `recordRun_zero` | Deleted; callers use `Segment.zero` after `record_headBox_iff`. |
| `recordRun_trans` | Deleted; callers use `Segment.trans`, with no dispatch added. |
| `recordRun_tagged` | Replaced by `recordStep_tagged_segment`, over `RecordSeg`; it consumes the supplied host prefix and dispatch. No host trace is duplicated. |
| `recordStep_empty_run` | Statement now uses `RecordSeg`. |
| `recordStep_phase_run` | Statement now uses `RecordSeg`. |
| `recordStep_reject_run` | Statement now uses `RecordSeg`. |
| `recordStep_read_all` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordEqNext` | Inventory prose-only hit in the following frozen public docstring; dispatch definition unchanged. |
| `recordStep_halt_run` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_copyback_run` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_state_run` | Statement now uses `RecordSeg`. |
| `recordStep_live_native` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`, `Segment.mono`. |
| `recordStep_seek_read` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_restore_native` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`, `Segment.mono`. |
| `recordStep_restore_digits` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_write_back` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_tape_run` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_prepare_native` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `recordStep_position_run` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`. |
| `exists_recordStepTM` | Body composes `RecordSeg` using shared segment operations; `recordSeg_iff` exports the frozen scalar cut/radius clauses. Statement and docstring unchanged. |
| `recordStep_read_prefix` | Statement now uses `RecordSeg`. Shared operations: `Segment.trans`, `Segment.mono`. |
| `recordStep_read_fields` | Statement now uses `RecordSeg`. Shared operations: `Segment.zero`, `Segment.trans`. |
| `exists_recordTestTM` | Body composes `RecordSeg` using shared segment operations; `recordSeg_iff` exports the frozen scalar cut/radius clauses. Statement and docstring unchanged. |
| `exists_recordEqTM` | Body composes `RecordSeg` using shared segment operations; `recordSeg_iff` exports the frozen scalar cut/radius clauses. Statement and docstring unchanged. |
| `recordStep_apply_run` | Statement now uses `RecordSeg`. Shared operations: `Segment.zero`, `Segment.trans`, `Segment.mono`. |


## Phase lemmas and contract status

`Segment.zero`, `Segment.trans`, and `Segment.mono` provide the shared zero, concatenation, and weakening arguments. The tagged helper uses `record_tag_ne` to exclude the two verdict stage tags. No second segment layer, phase host, seam, embedding transport, or row trace is introduced.

| Phase / shared helper | Contract status and remaining route | Verdict exclusion |
|---|---|---|
| `recordStep_empty_run` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_phase_run` | Shared host packaging uses `RecordSeg`; row-contract conversion remains at its consumers. | `phaseHostTM_run` once per invocation; `hi : ∀ b, i.1 ≠ .verdict b` is passed to the tagged-segment helper. |
| `recordStep_reject_run` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_read_all` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Inherited from component segments by `Segment.trans`; zero segments use the strict-cut API. |
| `recordStep_halt_run` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_copyback_run` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `copyTM_run_ofCfg`. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_state_run` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `scanTM_run_ofCfg`. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_live_native` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Inherited from component segments by `Segment.trans`; zero segments use the strict-cut API. |
| `recordStep_seek_read` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_restore_native` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_restore_digits` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_write_back` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `skipBackTM_run_ofCfg`. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_tape_run` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `scanTM_run_ofCfg`. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_prepare_native` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_position_run` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_read_prefix` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `copyTM_run_ofCfg`, `skipTM_run_ofCfg`. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_read_fields` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `skipBackTM_run_ofCfg`, `skipTM_run_ofCfg`. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_apply_run` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `scanTM_run_ofCfg`, `skipTM_run_ofCfg`. | Existing `recordStep_phase_run` stage inequalities and row exit cuts retained. |
| `recordStep_tagged_segment` | Phase 1 complete: packages the supplied phase-host prefix and dispatch as the shared segment. | The single record_tag_ne argument excludes both Sigma stage tags strictly before the endpoint. |
| `recordStep_scan_preserves` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `scanTM_run_ofCfg`. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_clear_snapshot` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `clearTM_run_ofCfg`. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_clear_heads` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_seek_transport` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_map_snapshot` | Pending Phase 2; only the mechanical segment migration is claimed. Retained row calls: `scanTM_run_ofCfg`. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_save_run` | Named exception retained unchanged: exactly one direct `counterLoopTM_run_escape`; contract form belongs to MIG-15. | Original counter-loop cut, then existing transport/host packaging at consumers. |
| `recordStep_save_transport` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_arithmetic_transport` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_read_run` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing cut/transport argument retained; no new host trace. |
| `recordStep_probe_run` | Pending Phase 2; only the mechanical segment migration is claimed. Existing private specializations, supplied seek specification, or native leaf argument retained. | Existing cut/transport argument retained; no new host trace. |


The counter-loop exception is preserved: `recordStep_save_run` has exactly one direct `counterLoopTM_run_escape` call, and its body is unchanged. Its route through `recordStep_save_transport`, `recordStep_prepare_native`, `recordStep_live_native`, and `exists_recordStepTM` remains intact. MIG-15 still owns its contract form.

## Phase 4: all 173 binding ledger rows

Line numbers in this table are the base ledger's identifiers. “Pending” includes legacy sites mechanically carried through the segment swap; it does not claim that those sites have been repointed. The required published API is recorded for each remaining row.

| Base line | Declaration | Definition | Disposition / published API |
|---:|---|---|---|
| 407 | `recordRun_zero` | `MultiTapeTM.runFrom` | Removed with recordRun_zero; callers use Segment.zero. |
| 441 | `record_tag_ne` | `Cfg.mapState` | Cfg.mapState_state. |
| 444 | `record_tag_ne` | `Cfg.mapState` | Cfg.mapState_state. |
| 465 | `recordRun_tagged` | `Cfg.mapState` | Cfg.mapState_workTapePos in recordStep_tagged_segment. |
| 529 | `recordStep_digits_succ` | `counterWord` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: counterWord_succ, counterWord_zero (round 3). |
| 541 | `recordStep_digits_succ` | `decFixed` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: decFixed_nil/_true_cons/_false_cons (#118). |
| 545 | `recordStep_digits_succ` | `decFixed` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: decFixed_nil/_true_cons/_false_cons (#118). |
| 547 | `recordStep_digits_succ` | `incFixed` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: incFixed_nil/_false_cons/_true_cons (MIG-12 API). |
| 550 | `recordStep_digits_succ` | `decFixed` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: decFixed_nil/_true_cons/_false_cons (#118). |
| 552 | `recordStep_digits_succ` | `decFixed` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: decFixed_nil/_true_cons/_false_cons (#118). |
| 554 | `recordStep_digits_succ` | `incFixed` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: incFixed_nil/_false_cons/_true_cons (MIG-12 API). |
| 589 | `recordStep_window` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 591 | `recordStep_window` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 598 | `recordStep_window` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 618 | `recordStep_restrict` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 618 | `recordStep_restrict` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 619 | `recordStep_restrict` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 619 | `recordStep_restrict` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 625 | `recordStep_restrict` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 632 | `recordStep_restrict` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 637 | `recordStep_restrict` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 638 | `recordStep_restrict` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 639 | `recordStep_restrict` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 639 | `recordStep_restrict` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 666 | `recordStep_native_frame` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 717 | `recordStep_read_run` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 743 | `recordStep_save_orbit` | `roundOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ. |
| 747 | `recordStep_save_orbit` | `counterLoopOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ, through the abbreviation (exact / simp only; N3). |
| 747 | `recordStep_save_orbit` | `roundOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ. |
| 748 | `recordStep_save_orbit` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 748 | `recordStep_save_orbit` | `roundOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ. |
| 760 | `recordStep_save_orbit` | `counterLoopOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ, through the abbreviation (exact / simp only; N3). |
| 760 | `recordStep_save_orbit` | `roundOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ. |
| 761 | `recordStep_save_orbit` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 761 | `recordStep_save_orbit` | `roundOrbit` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: roundOrbit_zero/_succ. |
| 766 | `recordStep_save_orbit` | `Cfg.inputSymbol` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner. |
| 776 | `recordStep_input_blank` | `Cfg.inputSymbol` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner. |
| 778 | `recordStep_input_blank` | `Cfg.inputSymbol` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner. |
| 821 | `recordStep_probe_run` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 827 | `recordStep_probe_run` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 831 | `recordStep_probe_run` | `moveInputPos` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: moveInputPos_zero/_leftBoundary/_rightBoundary/_neg_of_ne_left/_pos_of_ne_right. |
| 839 | `recordStep_probe_run` | `moveInputPos` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: moveInputPos_zero/_leftBoundary/_rightBoundary/_neg_of_ne_left/_pos_of_ne_right. |
| 853 | `recordStep_probe_run` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 1189 | `recordStep_cell_shift` | `scanFold` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: scanResult_keep_keep (round 3). |
| 1189 | `recordStep_cell_shift` | `scanKeep` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: scanResult_keep_keep (round 3). |
| 1258 | `recordStep_tape_word` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 1520 | `recordStep_state_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1522 | `recordStep_state_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1524 | `recordStep_state_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1579 | `recordStep_phase_run` | `Cfg.mapState` | Cfg.mapState_workTapePos. |
| 1671 | `recordStep_read_prefix` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 1676 | `recordStep_read_prefix` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 1682 | `recordStep_read_prefix` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 1731 | `recordStep_read_prefix` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1782 | `recordStep_read_prefix` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1803 | `recordStep_read_prefix` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 1835 | `recordStep_read_prefix` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1850 | `recordStep_read_prefix` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 1996 | `recordStep_read_fields` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2047 | `recordStep_read_fields` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2094 | `recordStep_read_fields` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2150 | `recordStep_read_fields` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2160 | `recordStep_read_fields` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 2180 | `recordStep_read_fields` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 2211 | `recordStep_read_all` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 2253 | `recordStep_clear_snapshot` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2308 | `recordStep_halt_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2335 | `recordStep_halt_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2338 | `recordStep_halt_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2388 | `recordStep_seek_transport` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 2392 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2392 | `recordStep_seek_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2398 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2409 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2409 | `recordStep_seek_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2410 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2410 | `recordStep_seek_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2412 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2412 | `recordStep_seek_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2414 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2414 | `recordStep_seek_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2416 | `recordStep_seek_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2416 | `recordStep_seek_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2454 | `recordStep_map_snapshot` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2456 | `recordStep_map_snapshot` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2499 | `recordStep_empty_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2525 | `recordStep_reject_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2601 | `recordStep_save_transport` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2604 | `recordStep_save_transport` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2618 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2618 | `recordStep_save_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2620 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2620 | `recordStep_save_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2627 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2630 | `recordStep_save_transport` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 2639 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2640 | `recordStep_save_transport` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 2641 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2641 | `recordStep_save_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2644 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2644 | `recordStep_save_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2658 | `recordStep_save_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2661 | `recordStep_save_transport` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 2791 | `recordStep_prepare_native` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2792 | `recordStep_prepare_native` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2860 | `recordStep_seek_read` | `Cfg.inputSymbol` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner. |
| 2860 | `recordStep_seek_read` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2883 | `recordStep_seek_read` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 2954 | `recordStep_arithmetic_transport` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2956 | `recordStep_arithmetic_transport` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 2976 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2976 | `recordStep_arithmetic_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2977 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2977 | `recordStep_arithmetic_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2982 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2990 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2993 | `recordStep_arithmetic_transport` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 2994 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2994 | `recordStep_arithmetic_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 2997 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 2997 | `recordStep_arithmetic_transport` | `embedEmitCfg` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output. |
| 3006 | `recordStep_arithmetic_transport` | `Cfg.liftSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol. |
| 3009 | `recordStep_arithmetic_transport` | `MultiTapeTM.runFrom` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add. |
| 3087 | `recordStep_restore_digits` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3113 | `recordStep_restore_digits` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3117 | `recordStep_restore_digits` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3157 | `recordStep_restore_native` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3215 | `recordStep_restore_native` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3216 | `recordStep_restore_native` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3221 | `recordStep_restore_native` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3327 | `recordStep_observed_action` | `Cfg.workTapeSymbols` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.workTapeSymbols_eq. |
| 3335 | `recordStep_observed_action` | `MultiTapeTM.step` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: MultiTapeTM.step_of_some (round 3), step_of_halt. |
| 3337 | `recordStep_observed_action` | `MultiTapeTM.outputSymbol` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: MultiTapeTM.outputSymbol_of_some (round 3), outputSymbol_of_halt, step_output. |
| 3369 | `recordStep_tape_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3397 | `recordStep_tape_run` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 3459 | `recordStep_tape_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3462 | `recordStep_tape_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3483 | `recordStep_copyback_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3529 | `recordStep_copyback_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3532 | `recordStep_copyback_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3617 | `recordStep_write_back` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3629 | `recordStep_write_back` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3631 | `recordStep_write_back` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 3706 | `recordStep_position_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3744 | `recordStep_position_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3753 | `recordStep_position_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 3764 | `recordStep_position_run` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 3843 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 3915 | `recordStep_apply_run` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 4019 | `recordStep_apply_run` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 4024 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4026 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4034 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4037 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4042 | `recordStep_apply_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 4100 | `recordStep_apply_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 4101 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4120 | `recordStep_apply_run` | `Action.apply` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes. |
| 4154 | `recordStep_apply_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 4200 | `recordStep_apply_run` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 4220 | `recordStep_apply_run` | `FinTM.bufferTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol. |
| 4220 | `recordStep_apply_run` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4263 | `recordStep_apply_run` | `fieldsTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldsTape_of_nonneg/_of_neg/_nil/_cons_shift/_field/_of_length_le. |
| 4264 | `recordStep_apply_run` | `fieldsTape` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldsTape_of_nonneg/_of_neg/_nil/_cons_shift/_field/_of_length_le. |
| 4385 | `exists_recordStepTM` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4635 | `exists_recordEqTM` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4686 | `exists_recordEqTM` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 4904 | `exists_recordEqTM` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 4920 | `exists_recordEqTM` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 5119 | `exists_recordTestTM` | `Cfg.mapState` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2). |
| 5265 | `exists_recordTestTM` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 5284 | `exists_recordTestTM` | `fieldOffset` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le. |
| 5300 | `Cfg.inWindow_init` | `Cfg.init` | Pending Phase 4; legacy site retained or mechanically carried through the segment swap. Required API: Cfg.init_state/_inputPos/_workTapes/_workTapePos/_output. |


## Verification

- PASS: bootstrap 279/279 modules completed successfully; one recorded exit-137 attempt was retried.
- PASS: final sweep 279/279 modules; every final-source check exit 0. One failed pre-correction CfgRecord attempt is retained in the log.
- PASS: final sweep covers the complete 52-module downstream closure (including CfgRecord).
- PASS: exact base sorry-warning declarations: 83 in 21 modules, both sweeps.
- PASS: successful final checks have no CfgRecord warning, no error, and no new warning.
- All warnings (unchanged): 557.

The 227-name import probe was rerun against the final import context: exit 0, no errors or warnings. Axiom evidence prints all 21 public declarations and all 5 new private declarations from the final `CfgRecord.olean`; every axiom set is contained in `[propext, Classical.choice, Quot.sound]`. The private probe checks the module prefix and requires every requested private declaration to be found.

Lint: **style_lint: 0 FAIL, 32 WARN over 37 files**. No new line exceeds 100 characters. The pre-existing file-size warning remains justified by this brief's one-file ownership and explicit no-size-cap partial migration; splitting the module is outside this assignment.

Rule 10/11 checks and their diff grep output are included with the freeze log. There is no citation of `copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, or `incrementTM_run_overflow`, and no private `Build/Catalog` declaration. New proof reads use the published segment, box, and `Cfg.mapState_*` APIs. Legacy unfolding sites are explicitly listed as pending above; no full Phase 4 compliance is claimed.

Final sweep tail:

```text
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect
CHECK 277/279 TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
CHECK 278/279 TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/SpaceComplexity/Savitch.lean:81:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Savitch.lean:114:8: warning: declaration uses 'sorry'
EXIT 0 TCSlib/Complexity/SpaceComplexity/Savitch
CHECK 279/279 TCSlib/Complexity/SpaceComplexity
EXIT 0 TCSlib/Complexity/SpaceComplexity
PASS: 279/279 modules
```

## Duplication

Both prescribed v3 screens were run one at a time under `nice -n 10`, using the supplied population. The before output is byte-identical to the supplied baseline. The after screen was rerun after the final scalar-conversion correction and used a snapshot at the same population path, with the other population files unchanged; its source SHA-256 was checked against the delivered source before packaging.

```text
declarations screened: 870; copy pairs (target reproduces >= half of source): 437; reproduced text: 132,126 chars
declarations screened: 870; copy pairs (target reproduces >= half of source): 435; reproduced text: 131,544 chars
```

There are **no new pairs involving `CfgRecord`**, so no new-pair justification or 90%-copy factoring remains. The swap removes these two directed cross-file pairs:

| Target | Source | Base reproduced text |
|---|---|---:|
| `CfgRecord.lean::recordRun_trans` | `Basic.lean::Turing.Segment.trans` | 291/291 (100%) |
| `Basic.lean::Turing.Segment.trans` | `CfgRecord.lean::recordRun_trans` | 291/294 (99%) |

The duplicate local concatenation proof was deleted and its consumers now call `Segment.trans` directly. No in-file pair was removed at this Phase 1 boundary. Total reproduced text decreased by 582 characters, from 132,126 to 131,544; declarations screened remain 870.


## REPORT checklist

- [x] Phase reached, exact base, and ancestor check recorded.
- [x] Every supplied `RecordRun` use mapped to its replacement or prose-only disposition.
- [x] Each phase/helper's contract status and verdict exclusion recorded, including pending work.
- [x] Named counter-loop exception recorded; one direct call and unchanged route.
- [x] Every one of the 173 Phase 4 ledger rows has a resolved/removed or pending disposition.
- [x] Freeze evidence, unchanged 21 public statements/docstrings, and before/after counts included.
- [x] Rule 10/11 diff greps and successful import-probe rerun recorded.
- [x] Both screens, all new pair justifications, and removed in-file pairs recorded.
- [x] Final sweep tail, axiom prints, and lint result included.

The archive contains this report, the full modified source, the format-patch series, the base-prerequisite bundle, bootstrap and final sweep logs, freeze and axiom logs, both screen outputs, the required shim source, and `SHA256SUMS`. Probe, lint, rule, and packaging evidence is incorporated into those logs/report rather than shipped as additional deliverables.
