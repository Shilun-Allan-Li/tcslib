# MIG-12 continuation 1 — E-RES environment handoff

**Status: stopped for insufficient free disk. No continuation proof was changed or checked.**
This archive preserves the two supplied phase-1 commits at the required base. It is an
E-RES handoff, not a completed migration or a newly kernel-checked partial.

## Resource preflight and stop

The supplied v2.1 addendum was followed. Both attachment hashes match:

- Brief: `0ee25ec575151a13c35b198f3c032b17c9ccef533067a8a6649f591f01a92bc5`.
- Addendum v2.1: `2563c8d2ffed3e1fa268748edb017577522cec14a922ad2989d1aa974ab12d15`.

Initial preflight (`evidence/logs/preflight.log`): `nproc = 9`; cgroup v2 limit
8,589,934,592 bytes; anon 1,027,284,992, kernel 371,027,968, shmem 0 bytes.

```
memory in use = 1,027,284,992 + 371,027,968 + 0 = 1,398,312,960 bytes
headroom = 8,589,934,592 - 1,398,312,960 = 7,191,621,632 bytes = 6.697720 GiB
free disk = 16,558,292,992 bytes = 15.421112 GiB
```

The initial preflight passed. The clone, runtime/download directory, evidence and `/tmp`
are on the disk-backed `overlay` filesystem. No tmpfs was used. The later filesystem
measurement fell below 12 GiB while the toolchain download was in progress; the recorded
stop recheck (`evidence/logs/resource-stop.log`) gives:

```
memory in use = 1,239,232,512 + 491,880,448 + 0 = 1,731,112,960 bytes
headroom = 8,589,934,592 - 1,731,112,960 = 6,858,821,632 bytes = 6.387775 GiB
free disk = 11,254,972,416 bytes = 10.482010 GiB
required free disk = 12,884,901,888 bytes = 12 GiB
```

**Escalation E-RES:** available disk is below the required minimum. Memory is not the
stop reason: `oom = 0`, `oom_kill = 0`, and no Lean process ran or exited 137.
`memory.current` and page cache were not used as the shortage calculation.
The full memory counters and both `df` outputs are retained in the logs.

No dependency tree was copied, moved, merged, deduplicated, or reused from another session.
Only one checkout was created. No cleanup-and-retry condition was encountered: there was
no cache attempt, ENOSPC, corrupt olean or Lean crash. The stop came from the free-disk rule.

The Lean 4.25.0 release archive download completed before cancellation reached it. It was
not extracted or executed, and is not included in this delivery. `lake exe cache get` was
not run; a continuation must run it with `TAR_OPTIONS=--no-same-owner` after passing its
preflight. No package cache or bootstrap product was created here. No `lake build` ran.
Part 2 was not triggered: no Lean startup was attempted, no startup error was observed,
no shim was compiled or preloaded, and no Lean-specific environment variables were set.

## Repository identity and history

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`, checked out initially on
  `complexity/arora-barak-ch3-4`, never on main.
- Observed campaign tip: `0bf4f0856baec53a519742a82e2d53ef30bfb839`.
- Base: `96d60278e4fde29b986ec1d0e59cd07f768fe28a`.
- `git merge-base --is-ancestor BASE HEAD` succeeded at the campaign tip.
- The tip's `campaign/fills/mig12/briefs/mig12-fill-cfgrecord-cont1.md` matched the
  attachment after normalizing the base hash and `@ANCESTOR@` placeholders.
- Created `fill/mig12-cfgrecord-cont1` at exactly the base, verified before `git am`.
- Applied exactly the two supplied patches, in order. Resulting commits:

```
d1f0b51d572b35e3b57ae4a838a5c9665afc6771 MIG-12: import the authorized contract facade
50f9cd5aecd2404b89820f21ea264763456ebc3c MIG-12: retire CfgRecord bookkeeping onto Segment (phase 1)
```

- Head: `50f9cd5aecd2404b89820f21ea264763456ebc3c`.
- Owned file blob: `1c9d198f7f1a1ed2c4bdd6ec0a98c1d9a2c88b6c` (exact match).
- The patch series and bundle are against the base and contain these two commits only.
  Bundle verification passed; its sole prerequisite is the base.
- No rebase, merge, cherry-pick, push or PR was performed. No worker-authored source commit
  was made. Untracked files reported by Git were left untouched and excluded; see
  `evidence/logs/working-tree-status.log`.

## Work done and remaining

| Phase | Delivered state | Continuation work |
| --- | --- | --- |
| 1 | Supplied Segment migration applied, exact patched blob verified | None added here |
| 2 | Original phase proofs retained | 0 of 29 phase lemmas newly migrated; all remain |
| 4 | Supplied patch retains its 5 of 173 ledger resolutions | 0 of the remaining 168 rows newly resolved |
| 3 | Original public row compositions retained from phase 1 | All three row recompositions remain |

The file has no lexical `sorry`, `admit`, or `axiom` declaration after comment stripping.
The supplied patched blob is the same one the maintainer previously validated as
admission-free; this session makes no new kernel or axiom-closure claim.
There is no mathematical/API escalation: E-RES stopped the work before an attempted rewrite.
No promotion candidate or additional duplicated proof was introduced.

`recordStep_save_run` retains its one direct `counterLoopTM_run_escape` use. Its callers and
route are unchanged. No counter-loop contract was introduced.

The five inherited ledger resolutions are base rows 407 (`Segment.zero` replacing the old
zero helper), 441 and 444 (`Cfg.mapState_state`), 465 (`Cfg.mapState_workTapePos` in the tagged
helper), and 1579 (`Cfg.mapState_workTapePos` in the phase helper). Every other ledger row is
listed at the end of this report as pending, with the brief's published replacement lemma.

## Declaration inventory

All listed changes below belong to the supplied phase-1 patch, not new continuation work.
The file is 5,302 lines at the base and 5,310 after the patches: +8 against the base,
0 against the continuation's patched input. Counts are 21 public and 98 private in both.
The full-migration estimate of −1.6k to −2.1k lines is not achieved by this handoff.

| Change | Declaration | Role |
| --- | --- | --- |
| Added | `RecordSeg` | Specializes the shared Segment to the record verdicts and head box. |
| Added | `recordSeg_iff` | Reads that segment in the original scalar form. |
| Added | `recordStep_tagged_segment` | Renames the tagged-host packaging helper and states it over RecordSeg. |
| Added | `record_headBox_iff` | Relates the box API to the scalar absolute-radius condition. |
| Added | `record_headBox_mono` | Weakens the radius through the box API. |
| Removed | `RecordRun` | Retired by the supplied Segment migration. |
| Removed | `recordRun_mono` | Retired by the supplied Segment migration. |
| Removed | `recordRun_tagged` | Retired by the supplied Segment migration. |
| Removed | `recordRun_trans` | Retired by the supplied Segment migration. |
| Removed | `recordRun_zero` | Retired by the supplied Segment migration. |
| Changed body | `exists_recordEqTM` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `exists_recordStepTM` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `exists_recordTestTM` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_apply_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_copyback_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_empty_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_halt_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_live_native` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_phase_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_position_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_prepare_native` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_read_all` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_read_fields` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_read_prefix` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_reject_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_restore_digits` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_restore_native` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_seek_read` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_state_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_tape_run` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `recordStep_write_back` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |
| Changed body | `record_tag_ne` | Supplied phase-1 segment substitutions or API projection; no continuation edit. |

Every other declaration is unchanged. The module header and all public docstrings are
unchanged. The sole import addition is the first patch's authorized
`TCSlib.Complexity.TuringMachine.Build.Contract`; no other import changed.

## Verification and its limits

| Check | Result |
| --- | --- |
| Attachment SHA-256 values | PASS, both exact |
| Ancestor, exact base, supplied patches, head blob | PASS |
| Owned-file scope and source agreement | PASS, only `Build/CfgRecord.lean` differs from base |
| Frozen public statements and docstrings | PASS, 21/21 byte-identical; repository parser plus byte comparison |
| Comment-stripped admission scan | PASS, 0 occurrences |
| Forbidden R3 canonical row names | PASS, all six have 0 code occurrences |
| Bootstrap | NOT RUN, 0/280 modules |
| `CfgRecord` elaboration | NOT RUN |
| Final sweep / 83-entry sorry-warning comparison | NOT RUN, missing bootstrap products |
| Import probe (227 names) | NOT RUN |
| Axioms for publics/new privates and three row dependency walks | NOT RUN |
| Seal comparison | NOT RUN |
| Before v3 duplication screen | INTERRUPTED after E-RES, exit 130; no results emitted |
| After v3 duplication screen | NOT RUN |
| Style lint (static) | `style_lint: 0 FAIL, 30 WARN over 38 files` |
| Bundle verification / sole prerequisite | PASS |

The freeze log is `evidence/logs/freeze.log`; hygiene and forbidden-name checks are in
`hygiene.log`. The inherited `exists_recordStepTM` dependence on the two `Build/Embed`
privates remains unaddressed, as in the maintainer's review. Required Lean logs exist as
explicit NOT RUN records; their presence is not evidence of a successful run.

The before screen was started on the 12-file population with `nice -n 10`, with no overlapping
screen or Lean process from this task. It was interrupted when the disk stop was detected.
`screen-before.txt` and `screen-after.txt` state the missing results. The separately named
`screen-issued-baseline.txt` is copied from the issued inputs, not a local screen: 870
screened declarations, 435 pairs, 131,544 reproduced characters. No new pairs or removed
pairs are claimed from a fresh run. No continuation proof diff exists.

The following seal counts are **the supplied maintainer measurements at the same patched
blob**, not rerun here. The inherited explicit-site count is 73; the remaining binding ledger
has 168 rows. No after count was measured.

| Definition | Issued patched-input sites | Local after check |
| --- | ---: | --- |
| `Cfg.mapState` | 27 | Not run |
| `MultiTapeTM.runFrom` | 15 | Not run |
| `Cfg.liftSymbols` | 20 | Not run |
| `embedEmitCfg` | 12 | Not run |
| `fieldOffset` | 7 | Not run |
| `Action.apply` | 6 | Not run |
| `roundOrbit` | 3 | Not run |
| `FinTM.bufferTape` | 1 | Not run |
| `Cfg.inputSymbol` | 1 | Not run |
| `incFixed` | 1 | Not run |
| `scanKeep` | 1 | Not run |
| `scanFold` | 1 | Not run |
| `counterWord` | 1 | Not run |
| `Cfg.init` | 1 | Not run |
| `decFixed` | 0 | Not run |
| `moveInputPos` | 0 | Not run |
| `fieldsTape` | 0 | Not run |
| `MultiTapeTM.step` | 0 | Not run |
| `MultiTapeTM.outputSymbol` | 0 | Not run |
| `Cfg.workTapeSymbols` | 0 | Not run |

## Delivery and continuation

`fill-mig12-cfgrecord-cont1-cp1.zip` records the supplied phase-1 state and this E-RES report.
`fill-mig12-cfgrecord-cont1.zip` contains the same handoff contents. Each archive contains
`REPORT.md`, the full owned source, the two-patch format-patch series, a bundle with exactly
the required base prerequisite, the available and skipped-check logs, both screen-status
outputs, and `SHA256SUMS` covering every other member. No toolchain, dependency cache,
olean, compiled shim or unrelated source is shipped.

Resume on a host that passes the v2.1 preflight and has sufficient disk for its own pinned
toolchain and cache. Apply the two bundled patches only once. Run the cache with the required
TAR_OPTIONS, verify the package pins and cache probe, and bootstrap the ordered upstream
closure before checking proof changes. Then continue phases 2–4 under the original brief.

## Brief checklist

- [x] Preflight numbers and v2.1 calculation recorded, including the later E-RES trigger.
- [x] Base, ancestor, patches and exact patched blob recorded.
- [x] Work and remaining scope stated; no new phase rewrite or ledger resolution claimed.
- [x] Counter-loop exception retained and identified.
- [ ] Fresh before/after seals and explicit-site comparison — deferred by E-RES; inherited counts labeled.
- [x] Freeze log, line counts and declaration counts recorded.
- [x] Rule 10/11 scope and grep status recorded; no continuation source diff.
- [ ] Import-probe rerun and axiom walks — deferred by E-RES.
- [ ] Both completed v3 screens — before interrupted, after not run; no fresh pair claims.
- [ ] Successful final sweep and axiom prints — deferred by E-RES, log placeholders explicit.
- [x] Static lint result recorded.
- [x] Phase-1 E-RES checkpoint and final zip written.

## Remaining ledger rows

Every row below is pending. Line numbers refer to the brief's original base, and the API
column is copied from its binding ledger; no proof using these replacements was tested here.

| Base line | Definition | Declaration | Published replacement |
| ---: | --- | --- | --- |
| 529 | `counterWord` | `recordStep_digits_succ` | counterWord_succ, counterWord_zero (round 3) |
| 541 | `decFixed` | `recordStep_digits_succ` | decFixed_nil/_true_cons/_false_cons (#118) |
| 545 | `decFixed` | `recordStep_digits_succ` | decFixed_nil/_true_cons/_false_cons (#118) |
| 547 | `incFixed` | `recordStep_digits_succ` | incFixed_nil/_false_cons/_true_cons (MIG-12 API) |
| 550 | `decFixed` | `recordStep_digits_succ` | decFixed_nil/_true_cons/_false_cons (#118) |
| 552 | `decFixed` | `recordStep_digits_succ` | decFixed_nil/_true_cons/_false_cons (#118) |
| 554 | `incFixed` | `recordStep_digits_succ` | incFixed_nil/_false_cons/_true_cons (MIG-12 API) |
| 589 | `Action.apply` | `recordStep_window` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 591 | `Action.apply` | `recordStep_window` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 598 | `Action.apply` | `recordStep_window` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 618 | `Cfg.liftSymbols` | `recordStep_restrict` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 618 | `embedEmitCfg` | `recordStep_restrict` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 619 | `Cfg.liftSymbols` | `recordStep_restrict` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 619 | `embedEmitCfg` | `recordStep_restrict` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 625 | `Cfg.liftSymbols` | `recordStep_restrict` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 632 | `MultiTapeTM.runFrom` | `recordStep_restrict` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 637 | `Cfg.liftSymbols` | `recordStep_restrict` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 638 | `MultiTapeTM.runFrom` | `recordStep_restrict` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 639 | `Cfg.liftSymbols` | `recordStep_restrict` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 639 | `embedEmitCfg` | `recordStep_restrict` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 666 | `MultiTapeTM.runFrom` | `recordStep_native_frame` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 717 | `MultiTapeTM.runFrom` | `recordStep_read_run` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 743 | `roundOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ |
| 747 | `counterLoopOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ, through the abbreviation (exact / simp only; N3) |
| 747 | `roundOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ |
| 748 | `MultiTapeTM.runFrom` | `recordStep_save_orbit` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 748 | `roundOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ |
| 760 | `counterLoopOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ, through the abbreviation (exact / simp only; N3) |
| 760 | `roundOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ |
| 761 | `MultiTapeTM.runFrom` | `recordStep_save_orbit` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 761 | `roundOrbit` | `recordStep_save_orbit` | roundOrbit_zero/_succ |
| 766 | `Cfg.inputSymbol` | `recordStep_save_orbit` | Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 776 | `Cfg.inputSymbol` | `recordStep_input_blank` | Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 778 | `Cfg.inputSymbol` | `recordStep_input_blank` | Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 821 | `MultiTapeTM.runFrom` | `recordStep_probe_run` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 827 | `MultiTapeTM.runFrom` | `recordStep_probe_run` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 831 | `moveInputPos` | `recordStep_probe_run` | moveInputPos_zero/_leftBoundary/_rightBoundary/_neg_of_ne_left/_pos_of_ne_right |
| 839 | `moveInputPos` | `recordStep_probe_run` | moveInputPos_zero/_leftBoundary/_rightBoundary/_neg_of_ne_left/_pos_of_ne_right |
| 853 | `MultiTapeTM.runFrom` | `recordStep_probe_run` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 1189 | `scanFold` | `recordStep_cell_shift` | scanResult_keep_keep (round 3) |
| 1189 | `scanKeep` | `recordStep_cell_shift` | scanResult_keep_keep (round 3) |
| 1258 | `Action.apply` | `recordStep_tape_word` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 1520 | `Cfg.mapState` | `recordStep_state_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1522 | `Cfg.mapState` | `recordStep_state_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1524 | `Cfg.mapState` | `recordStep_state_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1671 | `fieldOffset` | `recordStep_read_prefix` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 1676 | `fieldOffset` | `recordStep_read_prefix` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 1682 | `fieldOffset` | `recordStep_read_prefix` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 1731 | `Cfg.mapState` | `recordStep_read_prefix` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1782 | `Cfg.mapState` | `recordStep_read_prefix` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1803 | `FinTM.bufferTape` | `recordStep_read_prefix` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 1835 | `Cfg.mapState` | `recordStep_read_prefix` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1850 | `Cfg.mapState` | `recordStep_read_prefix` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 1996 | `Cfg.mapState` | `recordStep_read_fields` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2047 | `Cfg.mapState` | `recordStep_read_fields` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2094 | `Cfg.mapState` | `recordStep_read_fields` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2150 | `Cfg.mapState` | `recordStep_read_fields` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2160 | `fieldOffset` | `recordStep_read_fields` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 2180 | `fieldOffset` | `recordStep_read_fields` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 2211 | `fieldOffset` | `recordStep_read_all` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 2253 | `FinTM.bufferTape` | `recordStep_clear_snapshot` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2308 | `Cfg.mapState` | `recordStep_halt_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2335 | `Cfg.mapState` | `recordStep_halt_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2338 | `Cfg.mapState` | `recordStep_halt_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2388 | `MultiTapeTM.runFrom` | `recordStep_seek_transport` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2392 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2392 | `embedEmitCfg` | `recordStep_seek_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2398 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2409 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2409 | `embedEmitCfg` | `recordStep_seek_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2410 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2410 | `embedEmitCfg` | `recordStep_seek_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2412 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2412 | `embedEmitCfg` | `recordStep_seek_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2414 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2414 | `embedEmitCfg` | `recordStep_seek_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2416 | `Cfg.liftSymbols` | `recordStep_seek_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2416 | `embedEmitCfg` | `recordStep_seek_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2454 | `FinTM.bufferTape` | `recordStep_map_snapshot` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2456 | `FinTM.bufferTape` | `recordStep_map_snapshot` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2499 | `Cfg.mapState` | `recordStep_empty_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2525 | `Cfg.mapState` | `recordStep_reject_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2601 | `FinTM.bufferTape` | `recordStep_save_transport` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2604 | `FinTM.bufferTape` | `recordStep_save_transport` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2618 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2618 | `embedEmitCfg` | `recordStep_save_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2620 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2620 | `embedEmitCfg` | `recordStep_save_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2627 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2630 | `MultiTapeTM.runFrom` | `recordStep_save_transport` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2639 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2640 | `MultiTapeTM.runFrom` | `recordStep_save_transport` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2641 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2641 | `embedEmitCfg` | `recordStep_save_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2644 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2644 | `embedEmitCfg` | `recordStep_save_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2658 | `Cfg.liftSymbols` | `recordStep_save_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2661 | `MultiTapeTM.runFrom` | `recordStep_save_transport` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2791 | `Cfg.mapState` | `recordStep_prepare_native` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2792 | `Cfg.mapState` | `recordStep_prepare_native` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2860 | `Cfg.inputSymbol` | `recordStep_seek_read` | Cfg.inputSymbol_of_zero/_of_end, inputSymbolInner |
| 2860 | `Cfg.liftSymbols` | `recordStep_seek_read` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2883 | `Cfg.mapState` | `recordStep_seek_read` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 2954 | `FinTM.bufferTape` | `recordStep_arithmetic_transport` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2956 | `FinTM.bufferTape` | `recordStep_arithmetic_transport` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 2976 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2976 | `embedEmitCfg` | `recordStep_arithmetic_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2977 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2977 | `embedEmitCfg` | `recordStep_arithmetic_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2982 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2990 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2993 | `MultiTapeTM.runFrom` | `recordStep_arithmetic_transport` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 2994 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2994 | `embedEmitCfg` | `recordStep_arithmetic_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 2997 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 2997 | `embedEmitCfg` | `recordStep_arithmetic_transport` | embedEmitCfg_eq, _selected_tape/_pos, _unselected, _state/_inputPos/_output |
| 3006 | `Cfg.liftSymbols` | `recordStep_arithmetic_transport` | Cfg.liftSymbols_state/_inputPos/_workTapes/_workTapePos/_output/_inputSymbol |
| 3009 | `MultiTapeTM.runFrom` | `recordStep_arithmetic_transport` | runFrom_zero, runFrom_succ_eq_step, runFrom_succ_eq_step', runFrom_add |
| 3087 | `Cfg.mapState` | `recordStep_restore_digits` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3113 | `Cfg.mapState` | `recordStep_restore_digits` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3117 | `Cfg.mapState` | `recordStep_restore_digits` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3157 | `Cfg.mapState` | `recordStep_restore_native` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3215 | `Cfg.mapState` | `recordStep_restore_native` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3216 | `Cfg.mapState` | `recordStep_restore_native` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3221 | `Cfg.mapState` | `recordStep_restore_native` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3327 | `Cfg.workTapeSymbols` | `recordStep_observed_action` | Cfg.workTapeSymbols_eq |
| 3335 | `MultiTapeTM.step` | `recordStep_observed_action` | MultiTapeTM.step_of_some (round 3), step_of_halt |
| 3337 | `MultiTapeTM.outputSymbol` | `recordStep_observed_action` | MultiTapeTM.outputSymbol_of_some (round 3), outputSymbol_of_halt, step_output |
| 3369 | `Cfg.mapState` | `recordStep_tape_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3397 | `FinTM.bufferTape` | `recordStep_tape_run` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 3459 | `Cfg.mapState` | `recordStep_tape_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3462 | `Cfg.mapState` | `recordStep_tape_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3483 | `Cfg.mapState` | `recordStep_copyback_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3529 | `Cfg.mapState` | `recordStep_copyback_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3532 | `Cfg.mapState` | `recordStep_copyback_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3617 | `Cfg.mapState` | `recordStep_write_back` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3629 | `Cfg.mapState` | `recordStep_write_back` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3631 | `fieldOffset` | `recordStep_write_back` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 3706 | `Cfg.mapState` | `recordStep_position_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3744 | `Cfg.mapState` | `recordStep_position_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3753 | `Cfg.mapState` | `recordStep_position_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 3764 | `Action.apply` | `recordStep_position_run` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 3843 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 3915 | `FinTM.bufferTape` | `recordStep_apply_run` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 4019 | `Action.apply` | `recordStep_apply_run` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 4024 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4026 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4034 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4037 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4042 | `Cfg.mapState` | `recordStep_apply_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4100 | `Cfg.mapState` | `recordStep_apply_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4101 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4120 | `Action.apply` | `recordStep_apply_run` | Action.apply_state/_inputPos/_workTapePos/_output (round 3), Action.apply_workTapes |
| 4154 | `Cfg.mapState` | `recordStep_apply_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4200 | `Cfg.mapState` | `recordStep_apply_run` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4220 | `FinTM.bufferTape` | `recordStep_apply_run` | FinTM.bufferTape_nat/_left/_nil/_append/_map/_map_decode/_inputSymbol |
| 4220 | `fieldOffset` | `recordStep_apply_run` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4263 | `fieldsTape` | `recordStep_apply_run` | fieldsTape_of_nonneg/_of_neg/_nil/_cons_shift/_field/_of_length_le |
| 4264 | `fieldsTape` | `recordStep_apply_run` | fieldsTape_of_nonneg/_of_neg/_nil/_cons_shift/_field/_of_length_le |
| 4385 | `fieldOffset` | `exists_recordStepTM` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4635 | `fieldOffset` | `exists_recordEqTM` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4686 | `Cfg.mapState` | `exists_recordEqTM` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 4904 | `fieldOffset` | `exists_recordEqTM` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 4920 | `fieldOffset` | `exists_recordEqTM` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 5119 | `Cfg.mapState` | `exists_recordTestTM` | Cfg.mapState_state/_inputPos/_workTapes/_workTapePos/_output (#118 r2) |
| 5265 | `fieldOffset` | `exists_recordTestTM` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 5284 | `fieldOffset` | `exists_recordTestTM` | fieldOffset_zero/_succ/_cons_succ/_length/_add_length_le |
| 5300 | `Cfg.init` | `Cfg.inWindow_init` | Cfg.init_state/_inputPos/_workTapes/_workTapePos/_output |
