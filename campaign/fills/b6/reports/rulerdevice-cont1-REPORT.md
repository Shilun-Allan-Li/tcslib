# B6 F5 continuation 1 — final report

Outcome: **complete, with no admitted dependencies.** Both `Turing.exists_rulerDeviceTM`
and `Turing.exists_rulerHostTM` are proved. The earlier restoring boundary test is unchanged.
All three targets and all 32 new private declarations have clean axiom walks.

Base: `6cfee54474e3d954e3395f9d9eab5d025452a8dd`.
Branch: `fill/b6-rulerdevice-cont1`.
Branch created: 2026-10-22T06:15:31.325924+00:00.
Final commit: `0f57ba49bf3ca8e5017dfed11ea010d723498284`.
Item end: 2026-10-22T06:58:51.233487+00:00.
The ancestor check passed. All supplied attachment hashes and normalized repository briefs
were verified during the shared preflight. The first edit was the two authorized status
paragraphs, followed by this item's own full re-bootstrap. No code from item 1 was carried
into this branch. No rebase, merge, cherry-pick or push occurred.

Checkpoint 2 was delivered immediately after phase 2:
`fill-b6-rulerdevice-cont1-cp2.zip`, SHA-256
`6a91d02e4a7813325fe62cc410ef9883b35648f3e82d984d1bdeeb0a450c6f47`, commit
`8fa8598e`. Checkpoint 3 and the final ZIP contain the completed host and final verification.

## Phase 2: shared read and move rows

Both rows use one parameterized finite phase family. The concrete restoring test takes
`2ℓ + 2` steps, a stationary dispatch takes one, the public input-only leaf takes one, and
its final dispatch takes one. Thus the exact time is **2ℓ + 5**, and **C = 4** for ℓ > 0.
The same `rd_call_run` proof supplies both first-return cuts and the ruler-head bound.
It calls `phaseHostTM_run` twice; it introduces no new phase-host or seam iteration.

A read emits the blank result on yes and the restored native input symbol on no. A move
suppresses a left move on yes and otherwise uses the native clamped move. `rd_shift_move`
proves the physical/virtual identity through the public decrement and right-clamp equations.
The one-step `rd_callLeaf` uses `inputMoveAction` and `step_of_inputMoveAction`. Its stationary
instance is the read. There is no recreated catalog scan or action lemma.

| New private declaration | Role |
| --- | --- |
| `rd_test_window` | Projects unchanged tapes/output, the interval from head−1 to head+ℓ, liveness, and strict verdict avoidance from `rd_run`. |
| `rd_test_return` | Projects the exactly restored endpoint at `2ℓ + 2`. |
| `rd_answer` | Encodes three read results separately from the move result. |
| `rd_direction` | Suppresses only left movement at the tagged virtual boundary. |
| `rd_leafMove` | Selects stationary reading or the requested move. |
| `rd_leafAnswer` | Selects the read result or move exit code. |
| `rd_callLeaf` | Public input-only action leaf. |
| `rd_Phase` | Finite test, leaf, and final phase indices. |
| `rd_CallState` | Phase-tagged finite control carrier. |
| `rd_family` | Shared test/read/move phase family. |
| `rd_redirect` | Two stationary phase dispatches. |
| `rd_callTM` | Existing public phase-host constructor applied to that family. |
| `rd_call_run` | One exact-time, first-exit, and ruler-head argument for both rows. |
| `rd_shift_move` | Physical/virtual translation of both clamped boundaries. |
| `rd_tagged_read` | Tagged physical input equals the virtual cell, including the right blank. |


`rd_tagged_read` was generalized in phase 3 from one tape to arbitrary tape count, so the
host uses that same read argument. It was new in this fill; no inherited signature changed.

## Phase 3: the ruler host

The host has ordinary controls `(source state, boundary tag)` and paused controls carrying a
source successor and a test state. The ordinary step reads through the tag, moves the input
through `rd_direction`, performs the source action on `i.castSucc`, forwards its output, and
keeps the last ruler tape stationary and unwritten. The arbitrary source transition is read
through `MultiTapeTM.step_of_some` and the public `Action.apply_*` field equations.

Only a **live** left move from a cleared tag starts a test. R1 embeds `rd_test` on the last
tape, with the current bank/output as its frame. The guarded state-transport theorem maps
the final verdict directly to an ordinary source control, so there is no extra return
step. The test's time, cut, liveness, ruler interval, and unchanged fields are projections of
the inherited `rd_run`, not a repeated trace proof.

The encoding is `rulerHostCfg` with the canonical tag `decide (c.inputPos.val = 0)`. The cost
is **2ℓ + 3** when the selected action has a live successor, its current tag is false, and
its input move is left; otherwise the cost is **1**. In particular a halting source action
halts the host in that same step, with no pause. An already halted source has cost 1 and
both configurations stay absorbed. Every cost lies in `[1, 3(ℓ + 1)]`, giving **C = 3**.

Two instances of the public `Lockstep` structure share the single block lemma. The instance
with empty exit sets handles every source run, including times after halting. The instance
with `{none}` as its exit sets supplies the live cut. The selected host time is the sum of
block costs over `Finset.range t`. `Lockstep.runFrom`, `cut`, and `locate` provide the endpoint,
cut and intermediate-time location. The frame argument makes a nonrecursive zero/successor
split: locate in the penultimate prefix or split off the last block. Thus a post-step frame
always corresponds to a source time at most t, despite `locate` allowing a closed endpoint.

Visited-bank equality follows from `mem_visitedByTapeHead_iff`: intermediate frames give one
inclusion, and each encoded source endpoint at its cost-prefix sum gives the reverse.
The same membership API and the ruler envelope give the ruler subset `[rp−1, rp+ℓ]`.
The whole ruler tape is unchanged, including cells outside its finite window.

| New phase-3 private declaration | Role |
| --- | --- |
| `rd_HostState` | Finite ordinary/paused control carrier. |
| `rd_resume` | Maps a final test verdict directly to a source control. |
| `rd_pauseEmb` | Injective test-control map, with an explicit decoding left inverse. |
| `rd_slot` | Selects the last tape for R1. |
| `rd_slot_bank` | Every source-bank tape is outside that selection. |
| `rd_hostAction` | Source action on the bank and output, with the tagged input move and optional live pause. |
| `rd_hostTM` | Ordinary source branch and R1 test branch. |
| `rd_pause_run` | Exact test endpoint, liveness, bank/output frames and ruler interval via R1 and guarded transport. |
| `rd_host_source_step` | One source transition through the public action-field API. |
| `rd_next_tag` | Correct local tag when a live left-move pause is not needed. |
| `rd_hostEnc` | Canonically tagged `rulerHostCfg` encoding. |
| `rd_hostCost` | Positive cost, 1 or 2ℓ+3. |
| `rd_hostCost_bounds` | Uniform lower and upper cost bounds. |
| `rd_hostFrame` | Source-bank/output equality and unchanged, bounded ruler. |
| `rd_hostFrame_layout` | Encoded configurations satisfy that frame. |
| `rd_host_block` | One complete block's endpoint, cut and pre-/post-source frames. |
| `rd_host_frames` | Whole-run frames through `Lockstep.locate` and `runFrom`. |

The universal proofs include ℓ=1, z=[true], y=[] at positions 0 and 1, an empty payload at
the physical right blank, both coincident right clamps, and a source halting on a left move.
No nonempty payload, positive source tape count, liveness of the final successor, or
termination hypothesis was introduced. These cases are included by the proved statements;
no separate finite testing is substituted for their universal proofs.

## Scope and governance

The final source has **1282 lines, 15 public / 41 private declarations** (32 new private).
All 24 inherited declarations retain their statements; every non-target body is unchanged.
The five imports and public declaration count are unchanged. Both target docstrings were
restored byte-for-byte to the base by removing the temporary status paragraphs. The prefix
through the inherited test kit is byte-equal to the base. All new declarations are private
and begin `rd_`, in the two authorized homes. No added line exceeds 100 characters.

A seal with **17 external definitions** locally irreducible passes without warnings:
`MultiTapeTM.step`, `runFrom`, `outputSymbol`, `visitedByTapeHead`, `Action.apply`,
`Action.mapState`, `Cfg.mapState`, `moveInputPos`, `FinTM.bufferTape`, `Cfg.inputSymbol`,
`Cfg.workTapeSymbols`, `Cfg.init`, `tapeAction`, `inputMoveAction`, `phaseHostTM`,
`embedEmitCfg`, and `embedEmitTM`. The checkpoint's negative control fails as expected when
it attempts an `inputMoveAction` field by `rfl`. Every added rewrite, simplification and
`change` was inspected; only own definitions, local lets and standard Lean/Mathlib
constructors reduce. External TCSlib primitives and combinators use their published API.
The exact citation inventory and expanded import probe are included. No other-file private,
post-base declaration, R3 canonical row, new loop/seam iteration or embedding transport
proof is used. Historical failed development checks and the deliberate negative control are
retained as evidence; the final source and final validation are clean.

Axiom prints: all three targets and all 32 new private declarations, individually checked,
use only `[propext, Classical.choice, Quot.sound]` or a subset. **No `sorryAx` remains.**
No target or helper remains open. Escalations: **none**.

Promotion candidates: a generic source-step-plus-bounded-pause block contract, including the
two source frames, may help U2-E/F6; `rd_host_frames` demonstrates how to handle the closed
endpoint of `Lockstep.locate`. The physical clamped-move translation may be useful for
another input device. These are notes only; no upstream API was changed.

Lint: **0 FAIL, 31 WARN over 39 files**. The sole extra warning is InputDevice's size above
1,000 lines. The brief imposes no cap and restricts ownership to this file's two private
homes, so the proved private contracts remain beside their consumers. No implementation
was duplicated to obtain a smaller file, and no unauthorized split was made.

Fresh bootstrap: all 95 modules passed, exactly 33 sorry warnings in 14 modules;
maximum RSS 2,935,872 KiB and summed module wall time 511.652 seconds. The once-only
shared cache was not fetched again. Final sweep and screen numbers are recorded below.

## Shared environment

The once-only preflight passed: 9 CPUs; free disk 23,909,351,424 bytes; memory limit
8,589,934,592 bytes; anon+kernel+shmem 294,219,776 bytes; usable headroom 8,295,714,816 bytes;
oom=oom_kill=0. Free disk before this item was 17,553,752,064 bytes, above its 3 GiB floor.

Lean 4.25.0 and manifest-pinned packages are shared by the queue. The sole cache command was
narrowed to the union's 40 Mathlib roots, with `TAR_OPTIONS=--no-same-owner`: 35 new downloads,
1,002 unpacked files, exit 0, no failed downloads or empty oleans. Neither an unfiltered
cache fetch nor a project build was run. Every Lean check used `scripts/lean_check_tree.sh`,
with one Lean process at a time; screens ran one at a time under `nice -n 10`.

The original Lean binary could not locate its application. The exact addendum Part 2 shim
was used, SHA-256 `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
`LEAN_SYSROOT` and `LAKE_HOME` point to the fresh Lean archive; `LD_PRELOAD` is scoped to
Lean/Lake wrappers. The C source and logs are included; its binary is excluded. Timing/RSS
comes from sequential `os.wait4` because `/usr/bin/time` is unavailable.


The final archive contains two format-patch commits, the full modified source and a bundle
whose only prerequisite is the shared base, all reports and evidence, and SHA256SUMS. The
packaging check verifies ZIP CRCs and every manifest digest. The runtime shim binary and
all compiled Lean objects are excluded.

## Final validation results

The full 95-module sweep passed: **zero errors, 31 sorry warnings in 13 modules**, exactly
the bootstrap warning multiset minus the two owned targets, with every other warning
unchanged. Maximum RSS was **2,944,700 KiB** and summed module wall time **539.971 seconds**.
The owned module has zero warnings. The final **148-name probe** passed with zero errors
and zero warnings. The final 17-definition seal and all 35 axiom prints passed.

Before screen: 720 declarations, 488 pairs, 139,331 characters, byte-equal to the supplied
base. Final screen: **741 declarations, 489 pairs, 139,439 characters**. The only new pair is
the frozen `exists_rulerTestTM` proof reproducing 79% (108/136 characters) of the short
`rd_test_return` projection. Both use the same final specialization of `rd_run`; no trace
induction is repeated and the old target is frozen. There are no new phase-3 pairs, no new
cross-file pairs, and no new pair at 90% or above. **new copies: none**.

Checkpoint 3 was delivered while the sweep was still running:
`fill-b6-rulerdevice-cont1-cp3.zip`, SHA-256
`340bb49277955991e04e292b3419adef51602f8179b5dc3c5759195d317dded7`.
Its report explicitly identifies the partial sweep log and then-pending 148-name probe.
This final archive includes their completed results. The source commit is unchanged.
