# C1 bounded input window copier — environment-blocked delivery

**Status: E-RES, disk threshold at the cleaned-retry preflight. No kernel-checked proof progress.**
The initial preflight passed. The dependency fetch then failed with network CONNECT 403 errors.
The required cleanup was performed, but its new preflight found only **11.049571991 GiB** free,
below the required **12 GiB**. The cache retry and every dependent Lean check were therefore
stopped. Memory was not the blocker: the v2.1 calculation gave **7.510631561 GiB** of headroom,
with zero OOM events. This is an environment report, not a failed mathematical fill.

The executable source retains the original target and `sorry`; its only change is the permitted
implementation-status paragraph. A complete **unverified** proof draft is preserved verbatim in
Appendix C. That draft is not in the patch or bundle and must not be treated as a checked proof.

## Checkout and integrity

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Initially checked out `complexity/arora-barak-ch3-4`; observed tip
  `3de011c12bb05b97f572e6a7854a68f212125a4a`.
- `git merge-base --is-ancestor 96d60278e4fde29b986ec1d0e59cd07f768fe28a HEAD` succeeded there.
- The tip's `campaign/fills/c1/briefs/c1-fill-window-cont1.md` matched the attachment after
  substituting only its `@ANCESTOR@` placeholders. Its raw SHA-256 was
  `634a448e0957f57fca2f8c41b6cb9e18fa3512ab7f5e75284497297aab5931e4`.
- Created `fill/c1-window-cont1` at exactly base
  `96d60278e4fde29b986ec1d0e59cd07f768fe28a`.
- Delivery commit: `e71921d76ab6aad55e0a6b0480bccc3bb17cab89`.
- Brief SHA-256 verified:
  `980f5b5dcb62cf51828bf12f6affc81b1d62974a1697c7037b563686af2371aa`.
- Addendum **v2.1** SHA-256 verified:
  `2563c8d2ffed3e1fa268748edb017577522cec14a922ad2989d1aa974ab12d15`.
- No rebase, merge, cherry-pick, push or PR. One fresh checkout and one run-owned cache; no
  other session's toolchain, dependency tree, olean tree or object store was reused.

## Resource preflights and the stop

All quantities below are bytes; one GiB is 1,073,741,824 bytes. Both preflights recorded
`nproc = 9`. The clone, scratch, runtime, temporary directory and evidence directory are on
the same `overlay` filesystem, not tmpfs. Raw counters and filesystem output are in the logs.

| Quantity | Initial preflight | Cleaned-retry preflight |
| --- | ---: | ---: |
| `memory.max` | 8,589,934,592 | 8,589,934,592 |
| `memory.current`, informational only | 4,201,525,248 | 7,193,751,552 |
| `anon` | 114,511,872 | 103,677,952 |
| `kernel` | 139,902,976 | 421,777,408 |
| `shmem` | 0 | 0 |
| Memory in use | 254,414,848 | 525,455,360 |
| Headroom | 8,335,519,744 | 8,064,479,232 |
| Headroom in GiB | 7.763057709 | 7.510631561 |
| Available disk | 28,038,299,648 | 11,864,387,584 |
| Available disk in GiB | 26.112701416 | 11.049571991 |
| `oom` / `oom_kill` | 0 / 0 | 0 / 0 |
| Result | PASS | E-RES: disk |

The v2.1 calculation, explicitly:

```text
Initial use = 114,511,872 + 139,902,976 + 0 = 254,414,848.
Initial headroom = 8,589,934,592 - 254,414,848 = 8,335,519,744.

Retry use = 103,677,952 + 421,777,408 + 0 = 525,455,360.
Retry headroom = 8,589,934,592 - 525,455,360 = 8,064,479,232.
8,064,479,232 > 4 × 1,073,741,824 = 4,294,967,296: memory PASS.

12 × 1,073,741,824 = 12,884,901,888 required disk bytes.
11,864,387,584 < 12,884,901,888: disk FAIL.
Shortfall = 12,884,901,888 - 11,864,387,584 = 1,020,514,304 bytes.
```

Page cache and the `memory.events` `max` counter were never treated as a shortage. A progress
sample had `memory.current = 8,489,017,344` but still 7,096,451,072 bytes of valid headroom;
work continued. No OOM event or Lean exit 137 was observed. No claim is made about what caused
the available disk to decrease during the run.

## Runtime and dependency cache

The pinned Lean 4.25.0 release was freshly downloaded from its official release URL and
extracted with `tar --no-same-owner`. Archive SHA-256:
`97bee7bda676ca54f4b1cebe323242a08323d75134fecd1ba31cee4db66abb8a`.
The unmodified binary's first `--version` failed with `error: failed to locate application`.
Only then was the addendum's exact fallback compiled and used. The shim source hash matched
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
Its source is included at `evidence/runtime/executable-path.c`; no compiled shim is shipped.

Wrappers scoped the following variables to Lean/Lake invocations:

```text
LEAN_SYSROOT=/workspace/scratch/3bd72f71c7bd/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/3bd72f71c7bd/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/3bd72f71c7bd/runtime/executable-path.so
```

The shimmed binary printed Lean 4.25.0, commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. The prepared Lean wrapper selected `-j4` for module
checks; none of those checks ran. The cache invocation was:

```bash
PATH=/workspace/scratch/3bd72f71c7bd/runtime/bin:$PATH \
MATHLIB_CACHE_DIR=/workspace/scratch/3bd72f71c7bd/runtime/mathlib-cache \
TMPDIR=/workspace/scratch/3bd72f71c7bd/runtime/tmp \
TAR_OPTIONS=--no-same-owner lake exe cache get
```

The active dependency repositories matched every manifest URL and revision checked. The
optional documentation packages were absent, since the development configuration was not
selected; they were not supplied from another tree. The cache tool installed leantar and
fetched ProofWidgets, then reported **5,609 downloaded files and 1,897 failed downloads** out
of 7,506. Its exit code was **1**. The repeated failure was:

```text
Transfer failed (error code: 0): CONNECT tunnel failed, response 403
1897 download(s) failed
```

Under Part 1 item 4, this clone's `.lake/packages` and compiled Lake configurations were
deleted. Lake 4.25.0 placed its compiled configuration under `.lake/config/[anonymous]/`,
which was also cleaned. The new preflight failed the disk threshold, so **the second cache
invocation was not started**. No individual archive or olean was restored or unpacked by hand.
No dependency tree was copied, moved, merged or deduplicated. `lake build` was never invoked
by this worker; the cache tool's own expected ProofWidgets validation is covered by the
addendum's exception. No permission or toolchain patch was attempted beyond the exact shim.

**Escalations:** the fetch first encountered a network denial; the controlling final stop is
**E-RES, disk**. There is no established mathematical obstruction or missing-public-API claim.

## Ownership and declaration inventory

Only region (c) changes: the permitted `**Implementation status.**` paragraph. Regions (a)
and (b) are unchanged in the executable delivery. A comment-stripped comparison of the entire
owned file against the base is byte-identical. Imports, header, module docstring, public
statement, original proof sketch and original `sorry` are preserved. Other tracked files are
unchanged. Unrelated untracked files are not part of the patch, bundle or archive.

Final source: **88 lines**, **1 public theorem**, **0 private declarations**; no line exceeds
100 characters. **New executable declarations: none.** No body leaf is delivered as proved.
The status paragraph states only the open mathematical obligations and contains no campaign
labels, dates or session narrative.

The saved draft has **429 lines** and the following **16 unverified private declarations**.
Their names all have the required `iw_` prefix. The list records continuation work, not
accepted proof progress.

| Draft declaration | Intended role |
| --- | --- |
| `iw_body` | One-tape, one-cell copy leaf with blank-input escape |
| `iw_one` | Shared one-live-step calculation through public model equations |
| `iw_body_copy` | Successful symbol-copy step |
| `iw_body_blank` | Stationary blank-input escape step |
| `iw_patch` | Finite overwritten tape interval |
| `iw_patch_append` | Appending one copied symbol changes its next cell only |
| `iw_prefix` | Explicit body configuration after a copied prefix |
| `iw_prefix_zero` | Initial prefix configuration |
| `iw_prefix_step` | One-cell prefix extension |
| `iw_orbit` | Identify the public round orbit with the copied prefix |
| `iw_machine` | Existing counter loop with the prescribed escape-to-done join |
| `iw_join_prefix` | Transport runs before escape by public agreement |
| `iw_join_step` | One stationary join step via public control-action equation |
| `iw_patch_true` | Underflow's all-true counter word |
| `iw_local` | Two-tape exhaustion/escape assembly and time bounds |
| `iw_select` | Injective selection of destination and counter tapes |

The proposed leaf is needed because no catalog row provides the counter host's cyclic,
one-step native-input copy with an end-marker escape. The host, embedding and agreement
transport are reused. No second counter loop, embedding or general seam is proposed.

**Promotion candidate:** a generic counter-loop-over-one-step-body contract, with input seek
as another instance. This is a note, not a delivered shared declaration.

## Open target, proof sketch, and intended ledger

The sole open executable declaration is `Turing.exists_inputWindowCopyTM`.

**Proof sketch.** Use the prescribed one-tape leaf, returning to Boolean anchor `false`
after copying one input symbol and escaping to `true` at the right blank. For each available
prefix, prove the exact copied interval, input head, destination head and unchanged output.
Read the one-step round orbit through `roundOrbit_zero` and `roundOrbit_succ`. If the counter
expires first, apply `counterLoopTM_run_done`. If the input expires first, apply
`counterLoopTM_run_escape` with one additional blank-reading round. The local join agrees with
the counter loop away from its escape anchor, by `MultiTapeTM.agreeOn_iff` and
`runFrom_eq_of_agreeOn`; its single escape step uses `FinTM.controlAction_apply`. Finally
transport the two-tape result along the injection selecting `dst` and `j`, using
`embedEmitTM_runFrom` and `embedEmitCfg_eq`. Carry the first-arrival clause through both cases
and through the embedding. Appendix C drafts this whole route, but it has not elaborated.

The proposed constant is **C = 6**, not a kernel-verified witness. Write `d` for the counter
value, `y` for the available window, and `r = |y| + 1` in the early-end case. The arithmetic is:

```text
Exhaustion: |y| = d.
T = d + counterOverhead w (d + 1)
  ≤ d + (4d + 2|w| + 2)
  = 5d + 2|w| + 2
  ≤ 6(d + 1) + 2|w|.

Early input end: 1 ≤ r = |y| + 1 ≤ d.
T = r + counterOverhead w r + 1
  ≤ r + (4r + 2|w|) + 1
  = 5r + 2|w| + 1
  ≤ 6r + 2|w|.
```

The first bound uses `counterOverhead_le` once, including underflow. The second uses
`counterOverhead_le_of_le`. Exhaustion already reaches `done`, so the draft adds a join step
only on escape; even adding one on exhaustion would meet the brief's bound. Proposed final
counter words are `List.replicate w.length true` and `counterWord w (|y| + 1)` respectively.
The cases `d = 0`, `p = |z|`, `|y| < d`, and padded counter words are accounted for at the
source-planning level only; none has been kernel checked here.

## Verification and rule 10/11

- The 35-entry base sorry-warning list in 15 modules was read and recorded before proof edits;
  Appendix A reproduces it by name. No observed bootstrap warning set was obtained. Since the
  delivered executable Lean is unchanged, its source-level admission inventory is unchanged.
- The 81-module bootstrap was **not run**. The prepared upstream-first subset had 20 modules;
  the other 61 were to follow before the final sweep. Neither subset ran.
- The zero-sized-olean check, Mathlib smoke probe, owned-module checks, final sweep, import
  probe and axiom prints were **not run**: the cache-success gate failed, then the retry
  preflight stopped. No dependent check was attempted against missing prerequisites.
- No module was timed because no module check started. There were no self-imposed module
  timeouts. Logs were written directly to their final paths, never moved while in use.
- Axiom walk, **source-level only**:
  `Turing.exists_inputWindowCopyTM -> unchanged by sorry -> sorryAx`.
  There is no kernel axiom print and no claim that the allowed-axioms gate passed.
- There are no new private declarations in the executable delivery whose axioms need printing.
  The proposed target and all 16 draft privates would require prints on a continuation.
- Rule 10: the final added paragraph contains no external declaration citation or definition
  unfolding. The original 57-check probe and a prepared 96-check extension for the draft
  remained unrun. Appendix D gives that extension, enumerating the public names intended for
  the draft; these are not claims of successful elaboration.
- Rule 11 final-diff grep: no six-R3-row match and no other-file private-name match. The draft's
  raw private-name scan found only bound variables `S` and `T`, coinciding with unrelated
  single-letter private names in `CircuitSatReductionValid.lean`; no declaration from that
  file is used. No other file's private proof is cited.
- Static final checks: comment-stripped identity, owned-region check, `git diff --check`,
  declaration counts and line-length check **PASS**.
- Lint: `style_lint: 0 FAIL, 30 WARN over 38 files`, the base's result.

Final sweep log:

```text
FINAL SWEEP NOT RUN. Bootstrap prerequisites are unavailable; skipped under addendum Part 1
item 8. No check failures are claimed for modules that were not checked.
```

## Duplication

The final before/after v3 screens ran sequentially under `nice -n 10`, on the eight specified
population files. Both are byte-identical to the pinned base: **248 declarations, 102 pairs,
21,076 reproduced characters**. No new in-file or cross-file pair exists in the executable
delivery. **new copies: none**. Both full outputs are quoted in Appendix B.

The separate unverified-draft screen, after factoring the shared one-step argument, reported
264 declarations, 103 pairs and 21,150 reproduced characters, with no new cross-file pair.
Its sole new in-file pair was:

```text
InputWindow.lean::iw_body_copy reproduces InputWindow.lean::iw_body_blank: 74/119 = 62%
```

Justification: both specialize the shared `iw_one` calculation to the same body anchor and
select its scanned-symbol branch; their successful-copy and silent-escape conclusions differ.
This pair is absent from the executable delivery. Earlier draft screen results were not
substituted for the final before/after screens.

## Brief checklist

- [x] v2.1 preflight numbers, exact memory arithmetic and disk E-RES recorded.
- [x] Open target, obstruction, base hash and ancestor check recorded.
- [x] Nothing outside regions (a)–(c); final change is only region (c).
- [x] Final new-declaration inventory (none), separate draft inventory, leaf need and appendix.
- [x] Proposed C = 6 and both ledgers, explicitly not kernel verified.
- [x] Promotion candidate and environment escalations recorded.
- [x] Rule 10 citation inventory and rule 11 final-diff greps recorded.
- [ ] Import-probe rerun — blocked by failed cache gate and disk E-RES.
- [x] Both final screens quoted; no new pairs; **new copies: none**.
- [x] File size, declaration counts, final-sweep status and lint line recorded.
- [ ] Bootstrap, final Lean sweep and axiom prints — not run; E-RES blocks prerequisites.

## Delivery and checkpoints

The archive contains this report, the full modified source, one format-patch, a git bundle
whose sole prerequisite is the pinned base, the required logs, both final screen outputs,
the addendum's exact shim source, and `SHA256SUMS`. No dependency, olean, executable, compiled
shim or toolchain is shipped. `SHA256SUMS` covers every other archive entry.

Checkpoints were written after environment setup (`fill-c1-window-cont1-phase0.zip`) and after
the complete draft (`fill-c1-window-cont1-phase1-draft.zip`). The final environment-blocked ZIP
is the closing checkpoint. The latest draft is preserved in Appendix C, including edits made
after the earlier draft checkpoint. No claimed proof progress depends on an unsaved draft.

## Appendix A — base sorry-warning list

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

## Appendix B — full final screen outputs

Before:

```text
declarations screened: 248; copy pairs (target reproduces >= half of source): 102; reproduced text: 21,076 chars
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamReleaseTM_step_inr: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
```

After:

```text
declarations screened: 248; copy pairs (target reproduces >= half of source): 102; reproduced text: 21,076 chars
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamReleaseTM_step_inr: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
```

## Appendix C — complete unverified continuation draft

**NOT KERNEL CHECKED. Not part of the patch or bundle.** This is the full draft source as it
stood before the resource stop. Its syntax, tactic completion and axiom dependencies are not
certified. A continuation must elaborate and repair it under the same frozen statement and
import rules. The executable source elsewhere in this archive retains the original `sorry`.

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bounded input window copier

A counter-driven copy of a bounded window of the native input onto a work tape (user decision 5
of 2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)). The universal NDTM cannot
copy its whole input `x`, since its time bound has no `|x|` term; it copies the window
`x.take t` instead, and the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that
the window is enough for `t` simulated steps. The in-place suffix device stays with the
universal machine U-1, whose `universal` has no deadline to truncate by.

## Main definitions

No new definitions: the copier is the existential contract `Turing.exists_inputWindowCopyTM`.

## Main results

* `Turing.exists_inputWindowCopyTM` — the window copier's contract (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape.)
-/

namespace Turing

/-- The one-cell copy body returns to `false` after copying a symbol and escapes to `true`
at a blank. No catalog row provides this cyclic native-input copy with an end-marker escape. -/
private def iw_body : MultiTapeTM 1 Bool Bool where
  q₀ := false
  tr := fun q inp _ =>
    if q then FinTM.controlAction 0 (some true)
    else match inp with
      | none => FinTM.controlAction 0 (some true)
      | some b => ⟨1, fun _ => (some (some b), 1), none, some false⟩

/-- One live step of a leaf is its selected action, expressed through the model's equations. -/
private theorem iw_one {k : ℕ} {S : Type} {z : List Bool} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S z) (q : S) (hc : c.state = some q) :
    M.runFrom c 1 = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
  calc
    _ = M.step (M.runFrom c 0) := MultiTapeTM.runFrom_succ_eq_step'
    _ = _ := by rw [MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hc]

/-- One successful copy step writes the scanned bit, advances both heads and emits nothing. -/
private theorem iw_body_copy {z : List Bool} (c : Cfg 1 Bool Bool z) (b : Bool)
    (hc : c.state = some false) (hb : c.inputSymbol = some b) :
    iw_body.runFrom c 1 =
      { c with state := some false, inputPos := moveInputPos c.inputPos 1,
        workTapes := fun i => Function.update (c.workTapes i) (c.workTapePos i) (some b),
        workTapePos := fun i => c.workTapePos i + 1 } := by
  rw [iw_one iw_body c false hc]
  simp only [iw_body, Bool.false_eq_true, if_false, hb]
  apply Cfg.ext
  · rw [Action.apply_state]
  · rw [Action.apply_inputPos]
  · funext i
    simp only [Action.apply_workTapes, Option.getD_some]
  · funext i
    simp only [Action.apply_workTapePos, SignType.coe_one]
  · rw [Action.apply_output]
    exact List.append_nil _

/-- On a blank input cell, the body escapes in one step without changing any data. -/
private theorem iw_body_blank {z : List Bool} (c : Cfg 1 Bool Bool z)
    (hc : c.state = some false) (hb : c.inputSymbol = none) :
    iw_body.runFrom c 1 = { c with state := some true } := by
  rw [iw_one iw_body c false hc]
  simp only [iw_body, Bool.false_eq_true, if_false, hb,
    FinTM.controlAction_apply, moveInputPos_zero]

/-- Overwrite a finite interval of a tape, leaving its exterior intact. -/
private def iw_patch (tape : ℤ → Option Bool) (head : ℤ) (v : List Bool) :
    ℤ → Option Bool := fun q =>
  if head ≤ q ∧ q < head + (v.length : ℤ)
    then FinTM.bufferTape v (q - head) else tape q

/-- Appending a bit to the copied interval changes exactly its next cell.

**Proof sketch.** At the next cell use the buffer's append equation. Inside the old interval
that equation preserves the old symbol; outside the enlarged interval both tapes are framed. -/
private theorem iw_patch_append (tape : ℤ → Option Bool) (head : ℤ)
    (v : List Bool) (b : Bool) :
    iw_patch tape head (v ++ [b]) =
      Function.update (iw_patch tape head v) (head + (v.length : ℤ)) (some b) := by
  funext q
  by_cases he : q = head + (v.length : ℤ)
  · subst q
    rw [Function.update_same]
    simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one]
    rw [if_pos (by omega), FinTM.bufferTape_append]
    simp
  · rw [Function.update_noteq he]
    by_cases hi : head ≤ q ∧ q < head + (v.length : ℤ)
    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      rw [if_pos hi, if_pos (by omega), FinTM.bufferTape_append,
        Function.update_noteq (by omega)]
    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
        Nat.cast_one]
      rw [if_neg hi, if_neg (by omega)]

/-- The body configuration after copying `r` input cells starting at input index `p`. -/
private def iw_prefix {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
    (hr : p + r ≤ z.length) : Cfg 1 Bool Bool z where
  state := some false
  inputPos := ⟨p + 1 + r, by omega⟩
  workTapes := fun _ => iw_patch (c.workTapes 0) (c.workTapePos 0) ((z.drop p).take r)
  workTapePos := fun _ => c.workTapePos 0 + (r : ℤ)
  output := c.output

/-- The zero-length copied prefix is the initial configuration. -/
private theorem iw_prefix_zero {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hp : p ≤ z.length) (hc : c.state = some false) (hi : c.inputPos.val = p + 1) :
    iw_prefix c p 0 (by omega) = c := by
  apply Cfg.ext hc.symm
  · apply Fin.ext
    simpa only [iw_prefix, Nat.add_zero] using hi.symm
  · funext i q
    have hz : i = 0 := Subsingleton.elim _ _
    subst i
    simp [iw_prefix, iw_patch]
  · funext i
    have hz : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [iw_prefix, Nat.cast_zero, add_zero]
  · rfl

/-- A successful body round extends the copied input prefix by exactly one cell.

**Proof sketch.** The next input bit has index `p + r`. The one-step leaf writes it at the
next free destination cell, which is exactly the interval append equation. -/
private theorem iw_prefix_step {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
    (hr : p + r < z.length) :
    iw_body.runFrom (iw_prefix c p r (by omega)) 1 =
      iw_prefix c p (r + 1) (by omega) := by
  have hdrop : r < (z.drop p).length := by rw [List.length_drop]; omega
  have hlen : ((z.drop p).take r).length = r := List.length_take_of_le hdrop.le
  have hbit : (iw_prefix c p r (by omega)).inputSymbol = some z[p + r] :=
    inputSymbolInner (p + r) (by simp only [iw_prefix]; omega) hr
  rw [iw_body_copy _ _ rfl hbit]
  apply Cfg.ext rfl
  · apply Fin.ext
    rw [moveInputPos_pos_of_ne_right _ (by simp only [iw_prefix]; omega)]
    simp only [iw_prefix]
    omega
  · funext i
    simp only [iw_prefix]
    rw [List.take_succ_eq_append_getElem hdrop, List.getElem_drop, iw_patch_append, hlen]
  · funext i
    simp only [iw_prefix, Nat.cast_add, Nat.cast_one]
    omega
  · rfl

/-- The one-step round orbit is the explicitly copied prefix while input cells remain.

**Proof sketch.** Induct on the number of rounds using the public round-orbit equations and
the one-cell extension lemma. -/
private theorem iw_orbit {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (r : ℕ)
    (hr : p + r ≤ z.length) :
    counterLoopOrbit iw_body (fun _ => 1) c r = iw_prefix c p r hr := by
  induction r with
  | zero =>
    simpa only [roundOrbit_zero] using (iw_prefix_zero c p (by omega) hc hi).symm
  | succ r ih =>
    simp only [roundOrbit_succ]
    rw [ih (by omega)]
    exact iw_prefix_step c p r (by omega)

/-- The counter loop's escape anchor takes one silent stationary step to its done anchor.
Every other transition is delegated to the public counter loop. -/
private def iw_machine : MultiTapeTM 2 Bool (CounterLoopState Bool) where
  q₀ := .dec .run
  tr := fun q inp work => match q with
    | .escape => FinTM.controlAction 0 (some .done)
    | _ => (counterLoopTM iw_body false (some true)).tr q inp work

/-- Before the escape anchor is visited, adding the exit join does not change the run.

**Proof sketch.** The transition tables agree off the escape anchor. Apply the public
agreement transport on that set of states. -/
private theorem iw_join_prefix {z : List Bool} (c : Cfg 2 Bool (CounterLoopState Bool) z)
    (t : ℕ) (hcut : ∀ u < t,
      ((counterLoopTM iw_body false (some true)).runFrom c u).state ≠ some .escape) :
    iw_machine.runFrom c t = (counterLoopTM iw_body false (some true)).runFrom c t := by
  apply MultiTapeTM.runFrom_eq_of_agreeOn (Q := {q | q ≠ .escape})
  · apply (MultiTapeTM.agreeOn_iff _ _ _).mpr
    intro q hq inp work
    cases q with
    | escape => exact (hq rfl).elim
    | body _ => rfl
    | dec _ => rfl
    | done => rfl
  · intro u hu q hs he
    exact hcut u hu (hs.trans (congrArg some he))

/-- The join changes only the control state at the escape anchor. -/
private theorem iw_join_step {z : List Bool} (c : Cfg 2 Bool (CounterLoopState Bool) z)
    (hc : c.state = some .escape) :
    iw_machine.runFrom c 1 = { c with state := some .done } := by
  rw [iw_one iw_machine c .escape hc]
  simp only [iw_machine, FinTM.controlAction_apply, moveInputPos_zero]

/-- The all-true underflow word has exactly the counter loop's reported tape contents. -/
private theorem iw_patch_true (ct : ℤ → Option Bool) (cp : ℤ) (width : ℕ) :
    iw_patch ct cp (List.replicate width true) =
      fun q => if cp ≤ q ∧ q < cp + (width : ℤ) then some true else ct q := by
  funext q
  simp only [iw_patch, List.length_replicate]
  split_ifs with h
  · rw [FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
  · rfl

/-- The two-tape copier stops after the available window, with its counter width preserved.

**Proof sketch.** If the counter value fits in the remaining input, use the returning loop
contract and its whole-run underflow bound. Otherwise use the escape contract after one
additional blank-reading round, then the stationary exit join. Both contracts exclude an
earlier exit; their ledgers give the common coefficient six. -/
private theorem iw_local {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (hp : p ≤ z.length)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) → ct (cp + q) = FinTM.bufferTape w q)
    (n : ℕ) (hn : n = min (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)) :
    ∃ T ≤ 6 * (n + 1) + 2 * w.length, ∃ v : List Bool, v.length = w.length ∧
      iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done)
          (iw_prefix c p n (by have := Nat.min_le_right
            (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p); omega)) (iw_patch ct cp v) cp ∧
      ∀ u < T,
        (iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) u).state ≠ some .done := by
  let d := Nat.ofDigits 2 (w.map Bool.toNat)
  let start := counterLoopCfg (some (.dec .run)) c ct cp
  have horbit (r : ℕ) (hr : p + r ≤ z.length) := iw_orbit c p hc hi r hr
  by_cases hd : d ≤ z.length - p
  · have hnd : n = d := hn.trans (Nat.min_eq_left hd)
    subst n
    let t := d + counterOverhead w (d + 1)
    obtain ⟨hend, hcut, _, _⟩ := counterLoopTM_run_done iw_body false (some true)
      (fun _ => 1) c w ct cp hw d rfl (fun r hr => by
        refine ⟨?_, by decide, (fun u hu hu' => by omega), ?_⟩
        · rw [horbit r (by omega)]; rfl
        · rw [horbit (r + 1) (by omega)]; rfl) t (by simp [t])
    have hsame : iw_machine.runFrom start t =
        (counterLoopTM iw_body false (some true)).runFrom start t :=
      iw_join_prefix start t (fun u hu => (hcut u hu).2)
    refine ⟨t, ?_, List.replicate w.length true, List.length_replicate, ?_, ?_⟩
    · have hover := counterOverhead_le w
      change counterOverhead w (d + 1) ≤ 4 * d + 2 * w.length + 2 at hover
      dsimp only [t]
      omega
    · rw [hsame, hend, horbit d (by omega), iw_patch_true]
    · intro u hu
      rw [iw_join_prefix start u (fun s hs => (hcut s (by omega)).2)]
      exact (hcut u hu).1
  · have hnd : n = z.length - p := hn.trans (Nat.min_eq_right (by omega))
    have hpn : p + n = z.length := by omega
    have hnd' : n < d := by omega
    let t := n + 1 + counterOverhead w (n + 1)
    have hfinal : counterLoopOrbit iw_body (fun _ => 1) c (n + 1) =
        { iw_prefix c p n (by omega) with state := some true } := by
      simp only [roundOrbit_succ]
      rw [horbit n (by omega)]
      exact iw_body_blank _ rfl (Cfg.inputSymbol_of_end (by simp only [iw_prefix]; omega))
    obtain ⟨hend, hcut, _, _⟩ := counterLoopTM_run_escape iw_body false true (by decide)
      (fun _ => 1) c w ct cp hw n hnd' (fun r hr => by
        refine ⟨?_, by decide, (fun u hu hu' => by omega)⟩
        rw [horbit r (by omega)]; rfl) (by rw [hfinal]) t (by simp [t])
    have hsame (u : ℕ) (hu : u ≤ t) : iw_machine.runFrom start u =
        (counterLoopTM iw_body false (some true)).runFrom start u :=
      iw_join_prefix start u (fun s hs => (hcut s (by omega)).2)
    have hex : (iw_machine.runFrom start t).state = some .escape := by
      rw [hsame t le_rfl, hend, counter_cfg_eq]
    refine ⟨t + 1, ?_, counterWord w (n + 1), counterWord_length _ _, ?_, ?_⟩
    · have hover := counterOverhead_le_of_le w (n + 1) hnd'
      dsimp only [t]
      omega
    · rw [MultiTapeTM.runFrom_add, iw_join_step _ hex, hsame t le_rfl, hend, hfinal]
      simp only [counter_cfg_eq, iw_patch]
    · intro u hu
      by_cases hut : u < t
      · rw [hsame u (by omega)]
        exact (hcut u hut).1
      · have hut' : u = t := by omega
        subst u
        rw [hex]
        decide

/-- Select the destination as tape zero and the distinct counter as tape one. -/
private def iw_select {k : ℕ} (j dst : Fin k) (hjd : j ≠ dst) : Fin 2 ↪ Fin k :=
  ⟨fun i => if i = 0 then dst else j, by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

/-- **The bounded input window copier.** For work tapes `j ≠ dst` there is a machine with an
entry state `entry`, a live exit `done` and a constant `C` such that: started at `entry` with its
input head at native position `p + 1` (on the `p`-th input symbol) and a delimited binary counter
word `w` of value `d` on tape `j` from its head (little-endian, blanks at both ends, the
convention of `Turing.counterLoopTM`), it copies the window `y = (z.drop p).take d` (the next
`d` input symbols, fewer if the input ends) onto tape `dst` from that tape's head. It reaches
`done` within `C·(|y| + 1) + 2|w|` steps, and not before, with the input head just after the
window, the head of `dst` just after the copy, the counter head back at its start, the counter
word replaced by some word of the same width, and every other tape, head and the output
unchanged. No `|z|` term. (A leaf row of the construction layer; [AB09, §1.2].)

**Proof sketch.** `Turing.counterLoopTM` over a one-step body on the native input and tape
`dst`: at an input symbol, write it on `dst` and move both heads right, returning to the body's
anchor; at the input's right end, escape. Each round costs a fixed number of steps; the round
count is `|y|`, or `|y| + 1` when the input ends first. The counter ledger has two cases. On
exhaustion (`|y| = d`), the whole counter overhead of the `d + 1` decrements, the final
underflow included, is at most `4d + 2|w| + 2` (`Turing.counterOverhead_le`, used once). On
early input end (`|y| < d`), the loop escapes in round `r = |y| + 1 ≤ d`, after `r`
decrements, which cost at most `4r + 2|w|` (`Turing.counterOverhead_le_of_le`). Either way the
total is at most `C·(|y| + 1) + 2|w|`. The exit-time and endpoint clauses are those of
`Turing.counterLoopTM_run_done` and `Turing.counterLoopTM_run_escape`. -/
theorem exists_inputWindowCopyTM (k : ℕ) (j dst : Fin k) (hjd : j ≠ dst) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (W : MultiTapeTM k Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {z : List Bool} (d : Cfg k Bool Q z) (p : ℕ) (w : List Bool),
        d.state = some entry → d.inputPos.val = p + 1 →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes j (d.workTapePos j + q) = FinTM.bufferTape w q) →
        let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))
        ∃ T ≤ C * (y.length + 1) + 2 * w.length, ∃ w' : List Bool, w'.length = w.length ∧
          (W.runFrom d T).state = some done ∧
          (W.runFrom d T).inputPos.val = p + 1 + y.length ∧
          (W.runFrom d T).workTapes =
            Function.update (Function.update d.workTapes dst (fun q =>
              if d.workTapePos dst ≤ q ∧ q < d.workTapePos dst + (y.length : ℤ) then
                FinTM.bufferTape y (q - d.workTapePos dst)
              else d.workTapes dst q)) j (fun q =>
              if d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
                FinTM.bufferTape w' (q - d.workTapePos j)
              else d.workTapes j q) ∧
          (W.runFrom d T).workTapePos =
            Function.update d.workTapePos dst (d.workTapePos dst + (y.length : ℤ)) ∧
          (W.runFrom d T).output = d.output ∧
          ∀ u < T, (W.runFrom d u).state ≠ some done := by
  let ι := iw_select j dst hjd
  refine ⟨CounterLoopState Bool, inferInstance, inferInstance,
    embedEmitTM ι iw_machine, .dec .run, .done, 6, ?_⟩
  intro z c p w hc hi hw
  let body : Cfg 1 Bool Bool z :=
    ⟨some false, c.inputPos, fun _ => c.workTapes dst,
      fun _ => c.workTapePos dst, c.output⟩
  let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))
  have hp : p ≤ z.length := by have := c.inputPos.isLt; omega
  have hn : y.length = min (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p) := by
    simp only [y, List.length_take, List.length_drop]
  have hbound : p + y.length ≤ z.length := by
    have := Nat.min_le_right (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)
    omega
  have htake : (z.drop p).take y.length = y := by
    simpa only [y, List.length_take] using
      (List.take_eq_take_min (l := z.drop p) (i := Nat.ofDigits 2 (w.map Bool.toNat))).symm
  obtain ⟨T, hT, v, hv, hrun, hfirst⟩ :=
    iw_local body p rfl hi hp w (c.workTapes j) (c.workTapePos j) hw y.length hn
  let start := counterLoopCfg (some (.dec .run)) body (c.workTapes j) (c.workTapePos j)
  let finish := counterLoopCfg (some .done) (iw_prefix body p y.length hbound)
    (iw_patch (c.workTapes j) (c.workTapePos j) v) (c.workTapePos j)
  let out : Cfg k Bool (CounterLoopState Bool) z :=
    ⟨some .done, (iw_prefix body p y.length hbound).inputPos,
      Function.update (Function.update c.workTapes dst
        (iw_patch (c.workTapes dst) (c.workTapePos dst) y)) j
        (iw_patch (c.workTapes j) (c.workTapePos j) v),
      Function.update c.workTapePos dst (c.workTapePos dst + (y.length : ℤ)), c.output⟩
  have hstart : embedEmitCfg ι c.workTapes c.workTapePos [] start = c := by
    apply embedEmitCfg_eq
    · simpa only [start, counter_cfg_eq] using hc.symm
    · simp only [start, counter_cfg_eq, body]
    · simp only [start, counter_cfg_eq, body, List.nil_append]
    · intro i
      fin_cases i <;> simp [start, counter_cfg_eq, body, ι, iw_select]
    · intro i _
      exact ⟨rfl, rfl⟩
  have hend : embedEmitCfg ι c.workTapes c.workTapePos [] finish = out := by
    apply embedEmitCfg_eq
    · simp only [finish, counter_cfg_eq, out]
    · simp only [finish, counter_cfg_eq, out]
    · simp only [finish, counter_cfg_eq, iw_prefix, body, out, List.nil_append]
    · intro i
      fin_cases i <;>
        simp [finish, counter_cfg_eq, out, iw_prefix, body, ι, iw_select, htake, hjd,
          Ne.symm hjd]
    · intro i hnone
      have hd : i ≠ dst := by
        intro he
        apply hnone
        exact ⟨0, by simp [ι, iw_select, he]⟩
      have hj : i ≠ j := by
        intro he
        apply hnone
        exact ⟨1, by simp [ι, iw_select, he]⟩
      simp [out, hd, hj]
  have hlift (u : ℕ) : (embedEmitTM ι iw_machine).runFrom c u =
      embedEmitCfg ι c.workTapes c.workTapePos [] (iw_machine.runFrom start u) := by
    calc
      _ = (embedEmitTM ι iw_machine).runFrom
          (embedEmitCfg ι c.workTapes c.workTapePos [] start) u :=
        congrArg (fun d => (embedEmitTM ι iw_machine).runFrom d u) hstart.symm
      _ = _ := embedEmitTM_runFrom ι iw_machine c.workTapes c.workTapePos [] start u
  have he : (embedEmitTM ι iw_machine).runFrom c T = out := by
    rw [hlift T, hrun]
    exact hend
  refine ⟨T, hT, v, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [he, out]
  · simp only [he, out, iw_prefix]
  · rw [he]
    simp only [out, iw_patch, hv]
  · simp only [he, out]
  · simp only [he, out]
  · intro u hu
    rw [hlift u, embedEmitCfg_state]
    exact hfirst u hu

end Turing
```

## Appendix D — prepared extended import probe (not run)

```lean
import TCSlib.Complexity.TuringMachine.Build.InputWindow

/-! C1 wave 1, WC (the bounded input window copier, `Build/InputWindow`): every public declaration the
brief cites resolves from the owned file's import context (no import is added). -/

#check @Turing.exists_inputWindowCopyTM
#check @Turing.counterLoopTM
#check @Turing.counterLoopCfg
#check @Turing.counterLoopOrbit
#check @Turing.counterLoopTM_run_done
#check @Turing.counterLoopTM_run_escape
#check @Turing.counter_cfg_eq
#check @Turing.counterOverhead_le
#check @Turing.counterOverhead_le_of_le
#check @Turing.counterWord_zero
#check @Turing.counterWord_succ
#check @Turing.counterWord_value
#check @Turing.counterWord_length
#check @Turing.embedEmitTM
#check @Turing.embedEmitTM_runFrom
#check @Turing.embedEmitTM_frame
#check @Turing.embedEmitCfg_selected_tape
#check @Turing.embedEmitCfg_selected_pos
#check @Turing.embedEmitCfg_unselected
#check @Turing.embedEmitCfg_eq
#check @Turing.embedSilentTM
#check @Turing.embedSilentTM_runFrom
#check @Turing.embedSilentTM_frame
#check @Turing.MultiTapeTM.step_of_some
#check @Turing.MultiTapeTM.step_of_halt
#check @Turing.MultiTapeTM.runFrom_zero
#check @Turing.MultiTapeTM.runFrom_succ_eq_step'
#check @Turing.MultiTapeTM.runFrom_add
#check @Turing.Action.apply_state
#check @Turing.Action.apply_inputPos
#check @Turing.Action.apply_workTapePos
#check @Turing.Action.apply_output
#check @Turing.Action.apply_workTapes
#check @Turing.Cfg.mapState_state
#check @Turing.Cfg.mapState_inputPos
#check @Turing.Cfg.mapState_workTapes
#check @Turing.Cfg.mapState_workTapePos
#check @Turing.Cfg.mapState_output
#check @Turing.Cfg.inputSymbol_of_zero
#check @Turing.Cfg.inputSymbol_of_end
#check @Turing.Cfg.workTapeSymbols_eq
#check @Turing.moveInputPos_zero
#check @Turing.moveInputPos_pos_of_ne_right
#check @Turing.moveInputPos_rightBoundary
#check @Turing.FinTM.bufferTape
#check @Turing.FinTM.bufferTape_nil
#check @Turing.FinTM.bufferTape_nat
#check @Turing.FinTM.bufferTape_left
#check @Turing.FinTM.bufferTape_append

-- Continuation 1: the in-imports exit join (round 1's review)
#check @Turing.MultiTapeTM.agreeOn_iff
#check @Turing.MultiTapeTM.runFrom_eq_of_agreeOn
#check @Turing.MultiTapeTM.step_eq_of_agreeOn
#check @Turing.roundOrbit_zero
#check @Turing.roundOrbit_succ
#check @Turing.Cfg.ext
#check @Turing.embedEmitTM_tr
#check @Turing.inputSymbolInner

-- Additional declarations used by the fill.
#check @Turing.FinTM.controlAction
#check @Turing.FinTM.controlAction_apply
#check @Turing.FinTM.bufferTape_eq
#check @Turing.embedEmitCfg_state
#check @Turing.MultiTapeTM
#check @Turing.Cfg
#check @Turing.CounterLoopState
#check @Turing.counterLoopStateFintype
#check @Turing.FlagPhase.run
#check @Bool.false_eq_true
#check @Option.getD_some
#check @SignType.coe_one
#check @List.append_nil
#check @Function.update
#check @Function.update_same
#check @Function.update_noteq
#check @List.length_append
#check @List.length_singleton
#check @Nat.cast_add
#check @Nat.cast_one
#check @Nat.cast_zero
#check @Nat.add_zero
#check @Subsingleton.elim
#check @Fin.ext
#check @List.length_drop
#check @List.length_take_of_le
#check @List.take_succ_eq_append_getElem
#check @List.getElem_drop
#check @Nat.min_le_right
#check @Nat.min_eq_left
#check @Nat.min_eq_right
#check @List.replicate
#check @List.length_replicate
#check @List.getElem?_replicate_of_lt
#check @congrArg
#check @le_rfl
#check @Ne.symm
#check @List.length_take
#check @List.take_eq_take_min
```

## Notation

`d`: counter value; `w`: initial counter word; `y`: available requested input window;
`z`: native input; `p`: starting input index; `r`: body-round count; `T`: proposed total time;
`C`: proposed uniform coefficient; `|·|`: list length. In the draft, `c` is a configuration,
`ct` a counter tape, `cp` its head, `v` its proposed final word, and `ι` the two-tape selection.
