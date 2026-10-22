# C1 interpreter core, continuation 1 — E-RES environment report

**Disposition: E-RES; no completed proof phase.** The initial resource preflight passed. The
dependency-cache command then failed while installing its `leantar` helper. After the cleanup
required by addendum v2, the repeat preflight found **1,439,371,264 bytes (1.340519 GiB) of
memory headroom**, below the mandatory **4 GiB** threshold. Work stopped before the cache retry,
the Mathlib probe, or the bootstrap. This is an environment-blocked delivery, not a verified fill.

`Turing.exists_ndInterpreterCore` remains a direct `sorry`. The source retains the four
mandatory overlay drafts unchanged; their earlier maintainer verification is not an independent
check by this run. Two additional, unverified drafts written while cache setup was pending are
preserved only in this report's continuation appendix, not in the delivered Lean source.

## Inputs, checkout, and source

| Item | Result |
|---|---|
| Brief SHA-256 | `5fefa735a099d3f2d542747063bc3070ed1ef7445cc876e1d1462a614bd9f194` — matches |
| Addendum v2 SHA-256 | `2a80b0ef8da202cc5faf4c1513b2f34ed7437c5aef2cb3ed815355934b54ad2b` — matches |
| Cloned branch | `complexity/arora-barak-ch3-4` |
| Campaign tip observed | `9e89079e5676638de9fdc1994a705f471f8a97ae` |
| Brief at that tip | Matches the attachment after substituting `@ANCESTOR@` |
| Ancestor check | `git merge-base --is-ancestor 96d60278e4fde29b986ec1d0e59cd07f768fe28a HEAD` succeeded on the campaign branch |
| Exact base | `96d60278e4fde29b986ec1d0e59cd07f768fe28a` |
| Working branch | `fill/c1-core-cont1`, created directly at the base |
| Delivery commit | `dfb2106fbe190ae34326940e41773cd6c84e66ab` |
| First source edit | Byte-identical to `NDCodeSimulatorOverlay.lean.txt` |
| First-edit source SHA-256 | `e0d312eeb2048ba3dd4f33d7d6f8415b5a0cbcceb82c234b65707dc58c027135` |
| Final source SHA-256 | `ad97ca0ca553f38085422ea67f9ab5549bc2517c37ee53f52746c9dcaf21d03d` |
| Final source size | 252 lines; 3 public declarations, 4 private declarations |
| Phase checkpoints | None: no phase was completed. The final ZIP is the environment-stop checkpoint. |

There was no rebase, merge, cherry-pick, push, PR, `lake build`, or reuse of another session's
checkout, toolchain, package tree, or object store. All work used one clone. Only the owned
source is in the commit. An untracked temporary dataset file left by checkout is excluded from
the delivery and was not modified.

The three additional imports are exactly `Build.InputWindow`, `UniversalStartup`, and
`Build.SeamLayout`. The final source differs from the overlay only by the permitted
`**Implementation status.**` paragraph. Removing that paragraph recovers the overlay byte for
byte; removing the three imports and four drafts then recovers the pinned base byte for byte.
Thus the target's signature and body, the replay canonizer's signature and body, the original
docstrings, the bridge, and the module header remain frozen. No new added line exceeds 100
characters. Evidence: `evidence/logs/first-edit.log`, `checkout.log`, `scope-and-rules.log`, and
`source.diff`.

## Resource measurements and the mandatory stop

| Measurement | Initial preflight | Preflight after required cleanup |
|---|---:|---:|
| UTC | 2026-10-18 13:17:17 | 2026-10-18 13:25:39 |
| `nproc` | 9 | 9 |
| Filesystem type | overlay | overlay |
| Free disk, bytes | 31,352,131,584 | 22,431,014,912 |
| Free disk, GiB | 29.198948 | 20.890511 |
| `memory.max`, bytes | 8,589,934,592 | 8,589,934,592 |
| Printed `memory.current`, bytes | 829,464,576 | 7,150,563,328 |
| Logged memory headroom, bytes | 7,760,826,368 | 1,439,371,264 |
| Logged memory headroom, GiB | 7.227833 | 1.340519 |
| `memory.events`: `oom` / `oom_kill` | 0 / 0 | 0 / 0 |
| Result | PASS | **E-RES** |

The first script printed and then reread the moving memory counter; its logged headroom uses
the later sample. The repeat preflight's decisive calculation is

`8,589,934,592 − 7,150,563,328 = 1,439,371,264 < 4,294,967,296` bytes.

The later `memory.stat` snapshot attributes 6,689,075,200 bytes to file cache, with 84,193,280
bytes of anonymous memory. This explains much of the cgroup usage; it does not change the
addendum's required `limit − current` test. No OOM kill was observed. No attempt was made to
override that test, force reclaim, or make room by moving, copying, or deduplicating trees.

The logs include `df -B1` and `df -T` for the clone/workspace, runtime, evidence, uploads,
`/tmp`, and the cache helper directory. All were on the same disk-backed overlay filesystem;
no clone, package tree, olean tree, or `TMPDIR` was placed on tmpfs.

## Toolchain and cache sequence

1. No Lean executable was initially on `PATH`. The unmodified official Linux Lean 4.25.0
   release was downloaded into this workspace. The first tar extraction reported that it
   could not restore archived UID/GID 1001. Re-extraction of the same release with
   `tar --no-same-owner --zstd -xf …` succeeded. No toolchain source or binary was patched.
2. The pinned, unmodified `lean --version` then failed with exactly
   `error: failed to locate application`. This triggered addendum Part 2.
3. The addendum's C source was extracted exactly and compiled. Its SHA-256 is
   `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`, as required.
   With the authorized fallback, Lean reported version 4.25.0, commit
   `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, Release. The source is included under
   `evidence/runtime/`; the compiled `.so` and all build products are excluded.
4. Exactly one `lake exe cache get` was run in the clone. Its cache executable compiled, but
   installation of `leantar` failed with the tar ownership error quoted below. The command
   exited 1; a usable Mathlib cache was not established.
5. Before cleanup, every materialized package's origin URL and revision matched the manifest.
   Optional/inactive entries that Lake had not materialized are listed separately in the log.
   No package was re-cloned or updated over an existing mismatched package.
6. As addendum Part 1.4 requires after failure of its cache-success check, the clone's
   `.lake/packages` was deleted, and `.lake/lakefile.olean*` was checked for compiled
   configurations to delete. None matched. The repeat resource preflight then failed.
   **No second cache command was run**, because its resource precondition failed.
7. No module check was run against missing prerequisites. There was no bootstrap module
   timeout, stalled proof check, or compiler crash.

Exact runtime settings, applied through wrappers that launch Lean/Lake (not exported to
unrelated commands):

```text
PATH prefix=/workspace/scratch/19d6f69fa7b4/runtime/bin
LEAN_SYSROOT=/workspace/scratch/19d6f69fa7b4/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/19d6f69fa7b4/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/19d6f69fa7b4/runtime/executable-path.so
```

Cache failure captured by the execution tool:

```text
installing leantar 0.1.16
uncaught exception: failure in tar #[-xf, /root/.cache/mathlib/leantar-0.1.16.tar.gz,
  -C, /root/.cache/mathlib, --strip-components=1]:
tar: leantar: Cannot change ownership to uid 1001, gid 1001: Invalid argument
tar: Exiting with failure status due to previous errors
```

**Log limitation:** although the command used `2>&1 | tee` at the intended final path, its
cache log was observed to be zero bytes after completion. `cache-get-observed-transcript.log`
is explicitly labeled as reconstructed from the execution tool's captured output; it is not
presented as an original process log. The preflight, cleanup, package, checkout, and shim logs
were retained normally. The first toolchain extraction's ownership diagnostics were also
visible in the execution transcript rather than a retained extraction log; the successful
second extraction has its own log.

## Proof state and continuation

The required overlay contributes these private declarations; none was restated:

| Declaration | Role | Independent checking in this run |
|---|---|---|
| `ic_header_result` | Either nested-header projection, its output, position, and linear duration | Not reached |
| `ic_capture_return` | First-halt silent capture with a first live return | Not reached |
| `ic_replay_window` | Replay and input locality for any stream prefix within the window | Not reached |
| `ic_table_call` | Clean installation of the whole replay serialization, with a per-code cost | Not reached |

No phase is claimed complete:

1. **Startup:** the two captures, rewind, bank reconstruction, install call, and layout have
   not been composed. The tape choices `src`, `tbl`, and `sm` are not fixed. They must be
   distinct, with `src` a disposable scratch tape; the table and summary must reach the loop's
   mirrored bank through the published field equations and `Rep_iff`. The unverified layout
   specialization below retains these tapes as generic distinct parameters.
2. **Window:** counter duplication, the suffix-drop identity, the copier specialization, and
   the window rewind remain unassembled.
3. **Loop and verdict:** the represented replay start, hosted-loop invocation, and one-step
   verdict dispatch remain unassembled.
4. **Semantics and ledger:** `ic_replay_window` supplies the intended semantic bridge, but it
   has not been connected to a constructed interpreter. No actual final constant `C` has been
   constructed.

The brief's conditional coefficient remains the intended one:
`C = a + b + w + 50(L + 1) + 10`, with the layout cost absorbed into `a`. The planned bounds are

```text
T ≤ a + (b + 4)|bits t| + w(min(t, |x|) + 1) + (50(L + 1) + 4)t + 2
  ≤ C(t + 1), using |bits t| ≤ t;

T ≤ a + (b + 4)|bits t| + w(min(t, |x|) + 1) + (50(L + 1) + 4)t' + 2
  ≤ C(t' + |x| + |bits t| + 1), when the branch has halted by t' ≤ t.
```

These are continuation bookkeeping, **not proved runtime bounds for a constructed machine**.
Here `a` is a per-code startup constant, `b` its counter-width coefficient, `w` the window
coefficient, and `L` the replay table length, as in the brief and the previous report.

Open declarations and their literal proof sketches:

- `Turing.exists_ndInterpreterCore` — **Proof sketch:** compose fresh-bank returning captures
  of the two prefix projections with a native rewind. Preserve a second deadline counter;
  install the complete replay serialization and redistribute it with the shared layout
  machine. Copy and rewind the bounded input window. Establish the replay configuration's
  representation through the public equations, invoke the hosted loop, and dispatch its live
  exits using the summary cell. Use replay locality at the deadline and every early halting
  prefix, then discharge both time inequalities with one per-code constant.
- `Turing.exists_replayCanonizer` — out of scope, unchanged. **Proof sketch:** canonize the ND
  code, reserialize its two choice tables into the deterministic three-tape replay table via
  the primitive-recursive code transformation, then compose the computation contracts.
- `Turing.exists_inputWindowCopyTM` — external, unchanged. **Proof sketch:** run the shared
  counter loop over a one-symbol copy body, escaping when input ends and using the two
  counter-ledger bounds for exhaustion and early escape.
- `Turing.exists_seamLayoutTM` — external, unchanged. **Proof sketch:** use its prescribed
  eight phases to split the serialization header, unary state, and table; clear the source,
  restore the three heads, and retain the frame and first-exit clauses.

**Target axiom walk:** the delivered target body is still exactly `by sorry`; it does not
invoke any helper or replace the target's admission by an auxiliary admission. Thus this run
has not established a proof modulo the three authorized cited stubs. No kernel axiom print
was obtained. The brief reports standard axioms for the first three retained helpers, and
`sorryAx` via `exists_replayCanonizer` for `ic_table_call`; those are prior evidence only.

Promotion candidates, as required: the two-pass header split and the first-halt returning
capture. Neither was promoted. **Escalations: E-RES only.** No mathematical obstruction to
the frozen statement was established, and no proposed infrastructure gap is being claimed.

## Verification and checklist

| Required item | Result |
|---|---|
| Attachment hashes, tip-brief match, ancestor check, exact base | PASS |
| First edit, import restriction, frozen regions, private prefix | PASS by byte comparison |
| Every delivered private declaration listed | Four, above; all from the required overlay |
| Partial-status paragraph | Added only at the end of the target's docstring |
| Concrete layout tapes and assembled `Rep` | Not reached; explicitly open above |
| Final per-code constant and both runtime clauses | Not proved; conditional ledger only |
| Promotion candidates and escalations | Recorded above |
| Rule 10 citation inventory | `evidence/logs/citations.txt`; explicit source references only |
| Rule 10 rewrite inspection | Recorded in `rewrite-inspection.txt`; no additional delivered proof beyond the overlay |
| Import probe and seal test | SKIPPED after E-RES; not run against missing prerequisites |
| Rule 11 | Six canonical R3 names absent; no foreign private citation found |
| Before duplication screen | Matches the pinned screen base byte for byte |
| After duplication screen | See quoted output below and `screen-after.txt` |
| Source size | 252 lines; 3 public / 4 private |
| Style lint | `style_lint: 0 FAIL, 63 WARN over 80 files` |
| Cache probe, bootstrap, final sweep, axiom prints | NOT RUN / SKIPPED, with explicit logs |
| Phase checkpoint ZIPs | No phase completed; final ZIP is the stop checkpoint |
| Patch, bundle, source correspondence, ZIP checksums | See `delivery-integrity.log` and `SHA256SUMS` |

The foreign-private text search examined 5,010 distinct names. Its only matches were `T` and
`S`, locally bound variables here, not references to the unrelated private definitions with
those short names. No foreign private declaration is cited. The source inspection is not a
substitute for the unperformed seal test or a kernel proof-term inventory.

The bootstrap order was inspected but never executed. Its 81 modules partition into 36
upstream prerequisites of the overlaid owned file, the owned file, and 44 remaining modules.
None has a successful check in this run. The 35-entry base sorry set in 15 modules was recorded
by name before proof work and is reproduced below. No sorry was removed or introduced in the
delivered source, so the expected set is unchanged; this has not been confirmed by a sweep.

Final-sweep log:

```text
SKIPPED: mandatory E-RES stop; no dependency oleans or bootstrap products.
No failed downstream checks are being reported as findings.
```

## Duplication ledger

The v3 screens were run sequentially under `nice -n 10`, over the same 11-file population.
Only the permitted docstring paragraph differs from the overlay, so the screened declaration
bodies are unchanged. Both full outputs are quoted below. There are no new in-file pairs and
no new cross-file pairs. **new copies: none**.

## Base sorry set

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/Build/SeamLayout: 1: exists_seamLayoutTM
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

## Before screen

```text
declarations screened: 407; copy pairs (target reproduces >= half of source): 115; reproduced text: 43,357 chars
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/232 = 84%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/244 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/912 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   Loop.lean::emCall_right_run  reproduces  UniversalStartup.lean::universalCapture_run: 125/169 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   CodeSimulator.lean::exists_canonOffsetTM  reproduces  CodeSimulator.lean::exists_canonCountTM: 270/397 = 68%
   CodeSimulator.lean::exists_canonReadySeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   CodeSimulator.lean::exists_canonHeaderCountSeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   CodeSimulator.lean::canonEmbedWords  reproduces  Embed.lean::embedEmitCfg_ofWords_eq: 88/137 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Loop.lean::emCall_track_action  reproduces  UniversalStartup.lean::universalCapture_init: 211/334 = 63%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Loop.lean::loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   Embed.lean::embedEmitCfg_ofWords_eq  reproduces  CodeSimulator.lean::canonEmbedWords: 88/148 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   CodeSimulator.lean::canonStrictInstall  reproduces  CodeSimulator.lean::exists_canonHeaderSeam: 382/648 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Loop.lean::loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/161 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   CodeSimulator.lean::exists_canonHeaderSeam  reproduces  CodeSimulator.lean::canonStrictInstall: 382/671 = 57%
   Loop.lean::emCall_track_initial  reproduces  UniversalStartup.lean::universalCapture_init: 190/334 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   CodeSimulator.lean::scan_grammar_guard  reproduces  CodeSimulator.lean::canonScan_all: 152/278 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 460/912 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Loop.lean::emCall_track_stamp  reproduces  UniversalStartup.lean::universalCapture_init: 168/334 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
```

## After screen

```text
declarations screened: 407; copy pairs (target reproduces >= half of source): 115; reproduced text: 43,357 chars
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/232 = 84%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/244 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/912 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   Loop.lean::emCall_right_run  reproduces  UniversalStartup.lean::universalCapture_run: 125/169 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   CodeSimulator.lean::exists_canonOffsetTM  reproduces  CodeSimulator.lean::exists_canonCountTM: 270/397 = 68%
   CodeSimulator.lean::exists_canonReadySeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   CodeSimulator.lean::exists_canonHeaderCountSeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   CodeSimulator.lean::canonEmbedWords  reproduces  Embed.lean::embedEmitCfg_ofWords_eq: 88/137 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Loop.lean::emCall_track_action  reproduces  UniversalStartup.lean::universalCapture_init: 211/334 = 63%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Loop.lean::loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   Embed.lean::embedEmitCfg_ofWords_eq  reproduces  CodeSimulator.lean::canonEmbedWords: 88/148 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   CodeSimulator.lean::canonStrictInstall  reproduces  CodeSimulator.lean::exists_canonHeaderSeam: 382/648 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Loop.lean::loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/161 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   CodeSimulator.lean::exists_canonHeaderSeam  reproduces  CodeSimulator.lean::canonStrictInstall: 382/671 = 57%
   Loop.lean::emCall_track_initial  reproduces  UniversalStartup.lean::universalCapture_init: 190/334 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   CodeSimulator.lean::scan_grammar_guard  reproduces  CodeSimulator.lean::canonScan_all: 152/278 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 460/912 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Loop.lean::emCall_track_stamp  reproduces  UniversalStartup.lean::universalCapture_init: 168/334 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
```

## Unverified continuation drafts — not delivered as Lean source

These two drafts were written while the first cache setup was running. They were removed
from the owned source before delivery because no elaboration, axiom check, or seal test was
possible. They may need corrections. They should be attempted only on a host that passes the
required preflight and completes the pinned dependency bootstrap. They make no change to the
four mandatory overlay helpers or the target's proof state.

```lean
/-- A captured header projection returns silently, preserving every tape outside its fresh
bank and capture tape. Its input head is at the suffix, and its capture head follows the word.

**Proof sketch.** The header projection supplies a halted run with the desired output and
position. Capture its first halt and read the transport through its public field equations. -/
private theorem ic_capture_header {k : ℕ} (first : Bool) (α x : List Bool) (t : ℕ) :
    let M := prefixCanonTM
      (if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true)
    ∀ (ι : Fin M.k ↪ Fin k) (cap : Fin k), cap ∉ Set.range ι →
      ∀ (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (out : List Bool),
        let z := pairEncode (pairEncode (Nat.bits t) α) x
        let start :=
          (embedSilentCfg ι cap tapes heads [] out (M.tm.initCfg z)).mapState Sum.inl
        ∃ u ≤ 16 * (Nat.bits t).length + 8 * α.length + 25,
          let d := (embedSilentRetTM ι cap M.tm).runFrom start u
          d.state = some (Sum.inr ()) ∧
          d.inputPos.val = 4 * (Nat.bits t).length + 2 * α.length + 7 ∧
          d.workTapes cap = FinTM.bufferTape (if first then Nat.bits t else α) ∧
          d.workTapePos cap = ((if first then Nat.bits t else α).length : ℤ) ∧
          d.output = out ∧
          (∀ j, j ∉ Set.range ι → j ≠ cap →
            d.workTapes j = tapes j ∧ d.workTapePos j = heads j) ∧
          ∀ v < u, ((embedSilentRetTM ι cap M.tm).runFrom start v).state ≠
            some (Sum.inr ()) := by
  intro M ι cap hcap tapes heads out z start
  obtain ⟨halt, word, position⟩ := ic_header_result first α x t
  obtain ⟨u, bound, returned, cut⟩ := ic_capture_return M z ι cap hcap tapes heads out
    (16 * (Nat.bits t).length + 8 * α.length + 25) halt
  refine ⟨u, bound, ?_⟩
  dsimp only
  rw [returned]
  have captured := embedSilentCfg_cap ι cap hcap tapes heads [] out
    (M.tm.runFrom (M.tm.initCfg z) (16 * (Nat.bits t).length + 8 * α.length + 25))
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, cut⟩
  · rw [embedSilentCfg_inputPos]
    exact position
  · simpa only [word, List.nil_append] using captured.1
  · simpa only [word, List.nil_append] using captured.2
  · exact embedSilentCfg_output _ _ _ _ _ _ _
  · intro j hj hc
    exact embedSilentCfg_unselected ι cap tapes heads [] out _ j hj hc

/-- One layout machine installs each decoded replay table and initial summary, in a time
depending only on the code. The source begins at zero and is cleared; every other field is
framed by the layout contract.

**Proof sketch.** Specialize the serialization layout to the decoded replay machine. Its
initial state is the decoded machine's state. The two blank summary cells are obtained from
the negative cells of the unary word's buffer. -/
private theorem ic_layout_run (c : EffectiveNDMachineCode) (K : ℕ) (src tbl sm : Fin K)
    (hst : src ≠ tbl) (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM K Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ α : List Bool, ∃ T ≤ C * ((serializeK (c.decode α).tm.replayTM).length + 1),
        ∀ {z : List Bool} (d : Cfg K Bool Q z),
          d.state = some entry →
          d.workTapes src = FinTM.bufferTape (serializeK (c.decode α).tm.replayTM) →
          d.workTapePos src = 0 →
          d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
          d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
          (L.runFrom d T).state = some done ∧
          (L.runFrom d T).inputPos = d.inputPos ∧
          (L.runFrom d T).workTapes =
            Function.update (Function.update (Function.update d.workTapes src (fun _ => none))
              tbl (FinTM.bufferTape (tableBitsK (c.decode α).tm.replayTM.tr)))
              sm (StepBlock.summaryCells none (unaryFin (c.decode α).tm.q₀)) ∧
          (L.runFrom d T).workTapePos =
            Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0) sm 0 ∧
          (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
          ∀ u < T, (L.runFrom d u).state ≠ some done := by
  obtain ⟨Q, fQ, dQ, L, entry, done, C, layout⟩ :=
    exists_seamLayoutTM K src tbl sm hst hss hts
  refine ⟨Q, fQ, dQ, L, entry, done, C, fun α => ?_⟩
  have serial : serializeK (c.decode α).tm.replayTM =
      pairEncode (c.decode α).numStates.bits
        ((List.replicate (c.decode α).tm.q₀.val true ++ [false]) ++
          tableBitsK (c.decode α).tm.replayTM.tr) := by
    rw [serializeK_eq, NDTM.replayTM_q₀, unaryFin_eq]
  have summary :
      (fun p => FinTM.bufferTape
        (List.replicate (c.decode α).tm.q₀.val true ++ [false]) (p - 2)) =
      StepBlock.summaryCells none (unaryFin (c.decode α).tm.q₀) := by
    funext p
    rw [StepBlock.summaryCells_eq, unaryFin_eq]
    by_cases hp : p = 0
    · rw [hp, if_pos rfl]
      exact FinTM.bufferTape_of_neg _ (by omega)
    · rw [if_neg hp]
  obtain ⟨T, bound, run⟩ := layout (c.decode α).numStates.bits
    (tableBitsK (c.decode α).tm.replayTM.tr) (c.decode α).tm.q₀.val 0 (Nat.zero_le _)
  refine ⟨T, ?_, ?_⟩
  · simpa only [serial] using bound
  · intro z d he hs hp ht htp hm hmp
    simpa only [summary] using run d he (by simpa only [serial] using hs) hp ht htp hm hmp
```
