# C1-WC continuation 1: E-RES environment report

**Environment-only delivery. The target is not proved, and no new Lean proof was written or checked.**
The initial resource preflight passed; a later cgroup measurement fell below the mandatory
4 GiB headroom threshold. The cache fetch was interrupted with exit 130. No bootstrap,
Mathlib import probe, target check, downstream sweep, import-name probe, or axiom print ran.
This is E-RES, not a failed mathematical fill. The sole source change is the allowed
implementation-status paragraph. There is no proof contribution to land.

## Integrity and repository

| Item | Result |
|---|---|
| Attachment brief SHA-256 | `980f5b5dcb62cf51828bf12f6affc81b1d62974a1697c7037b563686af2371aa` — matches |
| Addendum v2 SHA-256 | `2a80b0ef8da202cc5faf4c1513b2f34ed7437c5aef2cb3ed815355934b54ad2b` — matches |
| Repository | `https://github.com/Shilun-Allan-Li/tcslib` |
| Campaign branch | `complexity/arora-barak-ch3-4` |
| Campaign tip observed | `9e89079e5676638de9fdc1994a705f471f8a97ae` |
| Campaign-tip brief comparison | Exact equality after replacing `@ANCESTOR@` with the base hash |
| Base | `96d60278e4fde29b986ec1d0e59cd07f768fe28a` |
| Ancestor check | `git merge-base --is-ancestor 96d60278e4fde29b986ec1d0e59cd07f768fe28a HEAD`, on the campaign branch: exit 0 |
| Fill branch | `fill/c1-window-cont1`, created at exactly the base |
| Delivery head | `1c0355f2b5de23b64503a3f97744073566a3c983` |
| Parent / series | One commit, whose parent is exactly the base; one format-patch |
| Bundle | `fill-c1-window-cont1.bundle`; sole prerequisite is the base; verified |

No push, PR, rebase, merge, or cherry-pick was performed. Attachments were read from their
provided local paths. One checkout and one dependency-fetch attempt were used; no dependency
tree was copied, moved, merged, deduplicated, or reused from another session.

## Resource measurements and escalation

The clone, toolchain, cache, evidence, temporary directory, and deliverables all reside on the
same disk-backed `overlay` filesystem. `nproc` returned **9**. No tmpfs was used.

| Measurement | Memory limit | Memory use | Headroom | Disk available |
|---|---:|---:|---:|---:|
| Initial preflight, 13:17:38 UTC | 8,589,934,592 B | 975,011,840 B | 7,614,922,752 B = 7.091949 GiB | 31,243,890,688 B = 29.098141 GiB |
| Post-toolchain snapshot, before cache launch | 8,589,934,592 B | 8,588,554,240 B | 1,380,352 B = 0.001286 GiB | 23,232,094,208 B |
| Resource-stop snapshot, 13:22:21 UTC | 8,589,934,592 B | 8,493,359,104 B | 96,575,488 B = 0.089943 GiB | 22,436,294,656 B |

Thresholds: disk **12,884,901,888 B (12 GiB)**; memory headroom **4,294,967,296 B (4 GiB)**.
The stop calculation was

```
8,589,934,592 − 8,493,359,104 = 96,575,488 < 4,294,967,296 bytes.
```

Initial `memory.events`: `low 0`, `high 0`, `max 0`, `oom 0`, `oom_kill 0`,
`oom_group_kill 0`. At the stop: `low 0`, `high 0`, `max 16852`, `oom 0`,
`oom_kill 0`, `oom_group_kill 0`.

The stop snapshot attributes 7,870,726,144 B to file cache, 199,225,344 B to anonymous memory,
and 421,416,960 B to kernel memory. Thus this was predominantly filesystem-cache accounting,
not an observed OOM kill or a Lean proof-check crash. I applied the addendum's literal
`memory.max − memory.current` test; I did not substitute an estimate of reclaimable memory.

**Sequencing deviation.** The post-toolchain snapshot was recorded in the same shell invocation
that launched the cache fetch, without an intervening threshold gate. It was already below
4 GiB, so the fetch should not have started. On inspecting the counters I stopped it.
No dependent elaboration was attempted. The initial passing preflight does not excuse that
missed later stop. A continuation should gate resource snapshots before launching the next
stage, rather than merely log them.

`evidence/logs/preflight.log` and `resource-stop.log` contain the raw byte counts, filesystem
types, and events. The fetch did not finish; no cache validation or successful cache result is
claimed. No cleaned retry was attempted: low headroom requires stopping, and none of the
addendum's retry-triggering cache-validation or Lean-crash checks was reached.

## Toolchain and authorized startup fallback

There was no preinstalled `lean`, `lake`, or `elan`. The official pinned Linux archive was
fetched from `https://github.com/leanprover/lean4/releases/download/v4.25.0/lean-4.25.0-linux.tar.zst`
and extracted into this request's scratch directory. The first extraction reported unsupported
archived UID/GID ownership changes; extracting the same toolchain archive with
`--no-same-owner` succeeded. No toolchain source or binary was patched.

The unmodified pinned executable then returned exactly:

```
error: failed to locate application
```

Part 2's exact C source was extracted from the addendum and compiled with
`cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so`.
Its SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
The source is included as `evidence/runtime/executable-path.c`; the compiled shared library
and all other build products are excluded.

Lean/Lake launcher wrappers applied these exact environment values only to Lean/Lake:

```
LEAN_SYSROOT=/workspace/scratch/e64f056dd76e/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/e64f056dd76e/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/e64f056dd76e/runtime/executable-path.so
```

The cache command's environment also used:

```
PATH=/workspace/scratch/e64f056dd76e/runtime/wrappers:/workspace/scratch/e64f056dd76e/runtime/lean-4.25.0-linux/bin:<inherited PATH>
TMPDIR=/workspace/scratch/e64f056dd76e/evidence/tmp
MATHLIB_CACHE_DIR=/workspace/scratch/e64f056dd76e/runtime/mathlib-cache
```

The successful version output was:

```
Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)
```

`/usr/bin/time` was unavailable: the initial timing-wrapper attempt exited 127 before Lake
started. The actual single cache attempt used a Python `resource.getrusage` timing wrapper.
It was interrupted under E-RES before an end-time/maximum-RSS summary could be printed.
The command session returned exit 130, recorded after its log writer stopped. No later Lake
command was run, so no later package-pin check was bypassed. No `lake build` was run.

## Source scope and declaration inventory

Only **region (c)** of `TCSlib/Complexity/TuringMachine/Build/InputWindow.lean` changed:
a mathematical implementation-status paragraph, with the comment closer on its own line.
The imports, module header, namespace, complete target statement, original `sorry`, and file
tail are byte-identical to the base. There are no new public or private declarations,
axioms, admissions, proof citations, or foreign-definition unfoldings.

- Base: 84 lines; final: **90 lines**, **1 public / 0 private declarations**.
- Longest added line: **95 characters**.
- Source SHA-256: `88bb321c9303365771db49c390364c995a9446bbc045328e5b7f20d65af16410`.
- `git diff --check`: passed.
- Added-diff grep for the six canonical R3 rows (`transferTM_run`, `copyTM_run`,
  `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`): no hits.
- Added-diff scan against other TCSlib files' private declaration names: no hits.

No body leaf was implemented. The prescribed leaf is still needed because whole-input copying
is not a one-step native-input copier returning to a counter-loop anchor. The only state changes
it should implement are `false → false` after copying a symbol and `false → true` on the right
input marker. It is to be a one-tape body, with the public counter loop adding the counter as
the second tape; R1 embeds those tapes at `dst` and `j`.

## Open declaration and continuation proof sketch

**Open declaration:** `Turing.exists_inputWindowCopyTM` (the sole original admission).

**Proof sketch.** Build the specified one-step native-input copying leaf, and prove its prefix
invariant for `(z.drop p).take r` using the public action, head, buffer, and round-orbit lemmas.
Use `counterLoopTM_run_done` when the requested window exhausts the counter, and
`counterLoopTM_run_escape` when the remaining input ends first. Redirect only the loop's escape
anchor to its done anchor in one stationary silent step; introduce the prefix agreement through
`MultiTapeTM.agreeOn_iff`, then use `runFrom_eq_of_agreeOn`. Embed the two-tape loop using
`embedEmitTM`. Use the public configuration reconstruction and field lemmas to obtain the
precise two updates and all frame clauses. Transfer the loop's first-arrival clauses through the
agreement and embedding. No import is needed; `phaseHostTM` is not an available route here.

This is continuation guidance, not checked proof text. The original docstring's literal
“Proof sketch” remains in the source. There are no other open declarations introduced by this work.

**Static axiom walk:** `exists_inputWindowCopyTM → original direct sorry → expected sorryAx`.
This is source inspection, not a kernel axiom print. No complete-delivery axiom claim is made.
There are no new privates to print.

## Constant and two ledgers

The planned constant remains **C = 6**, as the brief prescribes. Let `d` be the value of the
counter word `w`, and let `y = (z.drop p).take d`. The arithmetic below is explanatory;
it was not newly checked by Lean in this delivery.

On exhaustion, `|y| = d`. Counting a conservative extra join step gives

```
T ≤ d + counterOverhead w (d + 1) + 1
  ≤ d + (4d + 2|w| + 2) + 1
  = 5d + 2|w| + 3
  ≤ 6(d + 1) + 2|w|.
```

The prescribed join actually adds no step to the done case. On early input end, put
`r = |y| + 1`; then `1 ≤ r ≤ d`, and

```
T = r + counterOverhead w r + 1
  ≤ r + (4r + 2|w|) + 1
  = 5r + 2|w| + 1
  ≤ 6r + 2|w|
  = 6(|y| + 1) + 2|w|.
```

The width term is charged once in each case. The planned final word is the all-true word of
width `|w|` on exhaustion and `counterWord w (|y| + 1)` on escape. The cases `d = 0`,
`p = |z|`, `|y| < d`, and a counter padded with high zero bits remain obligations of the fill;
no new check of them is claimed.

Promotion candidate, note only: a generic counter-loop contract for a one-step returning or
escaping body, also applicable to input seek. No such helper was introduced here.
Escalations: **E-RES only**; no mathematical, statement, import, or API obstruction is claimed.

## Rule 10, verification, and base sorry set

New external declarations cited in proof text: **none**. No new private names or imports.
The 57-name issued import probe was not rerun because its prerequisites were unavailable;
`evidence/logs/import-probe.log` records non-execution. The supplied reference probe's
successful maintainer run is not being presented as this worker's verification.

The order list has **81 modules**: the owned-file import closure has 21 (including InputWindow),
with 60 remaining. **Zero** modules from either group were bootstrapped. The Mathlib import
probe, empty-olean scan, owned-file check, entire final sweep, and axiom prints were skipped
under the addendum's missing-prerequisite rule. Their logs say NOT RUN, not PASS or FAIL.

The base sorry-warning set was recorded by name before work. It has 35 declarations in 15 modules:

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

Static source comparison finds no change to any admitted proof. Therefore the expected warning
set is unchanged, but this was **not observed in a new Lean sweep**.

Final-sweep log, in full:

```text
NOT RUN: E-RES; required bootstrap and validated dependency cache are unavailable.
No dependent checks were attempted; no downstream failure is claimed.
```

Axiom log, in full:

```text
NOT RUN: E-RES; no fresh InputWindow.olean.
Static source walk only: Turing.exists_inputWindowCopyTM still has its original direct sorry.
Expected sorryAx dependency, not a fresh Lean axiom print. No new private declarations.
```

Lint command:
`python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`

```
style_lint: 0 FAIL, 30 WARN over 38 files
```

This matches the brief's lint baseline. No added line exceeds 100 characters.

## Duplication

Both declaration-keyed v3 screens ran sequentially, each under `nice -n 10`, on the issued
8-file population. Before, after, and the supplied base screen are byte-identical:
**248 declarations, 102 pairs, 21,076 characters**.
New owned-file cross-file pairs: none. New in-file pairs: none.
**new copies: none**. Both full outputs are quoted below, as required.

### Before

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

### After

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

## REPORT.md checklist

- [x] Preflight numbers, cgroup events, filesystems, later resource measurements and E-RES recorded.
- [x] Target status and obstruction; base hash, ancestor check and exact branch point recorded.
- [x] Nothing changed outside regions (a)–(c); only region (c) changed.
- [x] Every new declaration listed (none); unimplemented body leaf and rationale; appendix described.
- [x] Planned constant C = 6 and both ledgers recorded, explicitly not a new Lean result.
- [x] Promotion candidate and escalation recorded.
- [x] Rule 10 new proof-citation inventory (none), no-unfolding status, and Rule 11 diff scans recorded.
- [ ] Rule 10 import-probe rerun — blocked by E-RES, explicitly NOT RUN.
- [x] Both v3 screen outputs quoted, no new pairs, “new copies: none”.
- [x] Final file size and declaration counts; passing static lint and diff check recorded.
- [ ] Owned-file elaboration, final sweep and axiom prints — blocked by E-RES, explicitly NOT RUN.
- [x] Original open declaration named with a literal “Proof sketch” and honest static axiom walk.
- [x] Runtime fallback condition, exact source hash and environment values recorded; source included.
- [x] Report, full source, format-patch, one-base-prerequisite bundle, logs, screens and SHA256SUMS supplied.

## Archive contents and continuation

The ZIP root contains this report, the source at its repository path, one patch under `patches/`,
`fill-c1-window-cont1.bundle`, raw logs and both screen outputs under `evidence/logs/`,
the authorized fallback source under `evidence/runtime/`, and `SHA256SUMS` covering every other
member. No olean, binary runtime, compiled shim, dependency cache, attachment copy, or unverified
proof draft is shipped. The log files were written at their final evidence paths from the start
and were not moved while running.

Continue from the pinned base on a host that satisfies the addendum's resource test through
setup. This archive records an environment stop; its documentation-only commit is not a proof
partial that needs integration.

## Notation

`w`: initial binary counter word; `d`: its natural-number value; `z`: input word; `p`: initial
zero-based input index; `y`: requested available window; `r`: attempted body rounds on early
exit; `T`: total step count; `C`: planned time-bound coefficient; `|·|`: list length;
`GiB`: 2^30 bytes.
