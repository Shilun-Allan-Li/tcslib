# Emitter fill — Batch L

## Result and exact base

Completed the three targets in the required order: `exists_installCallTM`,
`exists_emitCallTM`, then `exists_emitLoopTM`. `Loop.lean` is admission-free.
No audited contract was renamed, re-signatured, restated, weakened, or removed.
No shared-lemma request or escalation is outstanding.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`
- Requested source branch: `complexity/arora-barak-ch1`
- Working branch: `fill/emitter-L`
- Required, object-verified base: `d7b5b6f94d28df8095165dd4dfe82fd09ba0d414`
- Source branch tip when cloned: `dd22fb9e33a17b81ce7f334c248c59893af17e48`.
  The brief at that tip required the earlier exact base above; only the new
  working branch was positioned at that base. The source branch was not changed.
- Final commit: `3511984efc05cc2075bee097eb4fb29247a4d195`
- Sole tracked change: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`
- Final source: 5713 lines; 119 new private declarations; no new public declarations.
- Final source SHA-256: `ef9c86dc0aef2eba3611527b3084a0472ce99a37532e64c9037ff8c6c6179ea8`

Delivery is this flat ZIP, with `SHA256SUMS` at its root. No push or PR was made.
The full source is named `Loop.lean` in the archive; the patch preserves its
repository path. The incremental bundle requires the exact base commit.

The committed brief and all binding documents were read. At the required base,
`audits/emitter-infra-r2-findings.md` is not a standalone file; its complete
verbatim contents were read from the committed round-3 audit bundle. The
round-3 findings and resolutions, including “Binding on the fill batches,”
were applied as the construction contract.

## Clean-call bridges

The two exports choose the same native controller, `emCallTM M emit`, with
`emit = false` for install and `emit = true` for emission. The physical layout
has a genuine argument tape, three components for each of the `M.k` source
work tapes, and a result-capture tape. In particular it remains positive when
`M.k = 0`. Neither `T` nor a witness runtime appears in this machine's native
transition table. Dispatch tests evaluator return states and cleaner return
states, using finite control to sequence the fixed bank count.

| Obligation | Discharging declarations |
| --- | --- |
| Prepare the tape-resident argument as virtual input; preserve the arbitrary native input head | `emCallEvalTM`, `emCall_eval_run`, `emCall_eval_initial`, `emCall_eval_first` |
| Track actual source-head displacements and visited intervals, including the terminal action | `emCallTrackTM`, `emCall_track_action`, `emCall_track_stamp`, `emCall_track_run`, `emCall_track_extent`, `emCall_track_support` |
| Normalize the virtual input head and cut evaluation to its actual first return | `emCallRightTM`, `emCall_right_endpoint`, `emCall_prepared_eval_first` |
| Restore initially blank scratch, without an overwritten-symbol history | `emCall_span_interval`, `emCall_track_clearable`, `emCall_clear_run`, `emCall_clear_first` |
| Relocate each cleaner into the host and preserve all inactive tapes/heads | `emCall_apply`, `emCall_relocate_run`, the layout inverse/disjointness lemmas |
| Clean every bank, with observed completion and charged dispatches | `emCall_bank_step`, `emCall_banks_run` |
| Install the result or emit it while retaining the argument; erase capture and rewind all relevant heads | `emCall_finish_arg`, `emCall_finish_rewind`, `emCall_finish_transfer`, `emCall_finish_erase`, `emCall_finish_run`, `emCall_finalize_run` |
| Full configuration equality at the fresh exit | `emCall_finish_final`, `emCall_complete` |
| Actual first positive exit | `emCall_exit_fixed`, `emCall_first` |

The track/clear and prepared-evaluation family was reimplemented in the owned
file from the proved `e3c*` templates in `ClassNP/Nondeterminism.lean`. Those
file-scoped private originals were neither edited nor referenced. Each source
work tape starts blank. Its support lies within the tracked interval; clearing
that interval and the two marker components therefore restores its entire
original tape, with all three heads at zero. This is exactly the audited
clean-seam restoration argument.

For argument length `a`, result length `b`, and deadline `T`, the full ledger is:

- Prepared evaluation and first bank dispatch: at most `2*T + a + 4`.
- All `M.k` banks, including their dispatches: at most `M.k * (6*T + 8)`.
- Finalizer dispatch, argument scan, capture rewind, transfer, erasure and rewind:
  exactly `a + 3*b + 6`.

`emCall_complete` bounds the sum by
`(24 + 13*M.k) * (T + a + b + 1)`, the audited
`6 + 13*M.k + 3*K` shape with `K = 6`. The fresh exit is absorbing and silent,
so taking its least visit retains the entire endpoint. The entry and exit
occupy disjoint control summands, giving positivity. Empty arguments, empty
results, and zero source tape count require no excluded cases.

## Emitting loop

`emLoopHost` keeps the existing fuel-capture/countdown skeleton, but its body
branch dispatches through `Turing.emitAction`. The former payload tape stays
blank and inactive. `emLoop_forward_apply` and `emLoop_forward_run` establish
native forwarding directly, including an emission on the final source action;
they do not cite the concurrent `Turing.emit_run` admission.

| Obligation | Discharging declarations |
| --- | --- |
| Arbitrary accumulated output is invisible to the transition table | `emLoop_step_prefix`, `emLoop_run_prefix` |
| Fuel capture and silent preparation | `emLoopHost_fuel_capture` through `emLoopHost_prepare` |
| Forward the stopped-body run with its exact tape/head endpoint | `emLoop_forward_run`, `emLoopHost_body_forward`, `emLoopHost_anchor_return`, `emLoopCall_frame` |
| Silent startup reaches round zero before any debit | `emLoopHost_start` |
| Silent fixed-width countdown works after an emitted chunk | `emLoopHost_borrow_step` through `emLoopHost_reject`, lifted by `emLoop_run_prefix` in `emLoopHost_round` |
| Per-round exact chunk, next clean seam, or final underflow with no verdict bit | `emLoopHost_round` |
| Concatenate ordered chunks after arbitrary output prefixes | New lemma `emLoop_sum` |
| Align native fuel and round indices | Local `words`, `orbit`, `hsuccess`, `hsegments`, and `hinit` in the export proof; proved existing `loopDebit_iterate_value` and `loopDebit_iterate_length` |

The emitted rounds are exactly `0..R`: startup enters round zero without
borrowing; rounds with index `< R` debit successfully after emission; round
`R` emits before underflow. The sum is over `R + 1 > 0` segments, hence `R = 0`
executes one round. Administrative transitions append no extra verdict bit.

Fuel/setup plus startup takes at most `10*(T+1)`. A source round takes at most
`T`; its stopped-anchor/debit segment is at most `T + 2*width + 5`, with
`width ≤ T`, hence at most `10*(T+1)`. `emLoop_sum` charges all `R+1` segments,
yielding the exported coefficient `10` in `10*(T+1)*(R+2)`.
The frozen empty-output `loop_run` is neither changed nor used by this export.

## Verification

- Final fresh sweep: **57/57 modules**, direct checks, **zero `error:` lines**,
  **57 fresh nonempty `.olean` files**. The remaining **17** admission warnings
  are exactly the untouched four concurrent emitter-spec admissions and thirteen
  campaign admissions; none are in `Loop.lean`.
- Kernel traversal: **125 named declarations** passed: the three targets,
  every one of the 119 new private helpers, and three proved regressions.
  Traversal follows checked declaration types, opaque bodies, and inductive
  constructors, with a hard failure on missing checked declarations.
- The three targets print exactly `[propext, Classical.choice, Quot.sound]`;
  all admission-root lists are empty. The audit additionally rejects any
  dependency of the new emitting loop on either frozen `loop_run` or the
  concurrent `Turing.emit_run`.
- `exists_loopCfgTM`, `exists_loopFindTM`, and `capture_run` retain standard
  axioms and empty admission roots.
- Statement/ownership freeze: PASS. `git diff --check`: PASS. Style lint:
  **0 FAIL, 2 documented size WARN**.
- The format-patch series was applied to an isolated Git index initialized at
  the exact required base. Its resulting complete tree equals the delivered
  commit tree. No worktree or other branch was switched during replay.
- `git bundle verify`: PASS; the bundle exports only `refs/heads/fill/emitter-L`
  and records the required base as its prerequisite.

Final sweep log tail:

```text
MODULE 55/57 TCSlib/Complexity/Formulas
PASS 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
PASS 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
PASS 57/57 TCSlib/Complexity/ClassNP
FINAL SWEEP PASS: 57/57 modules; 57 fresh nonempty .olean files.
```

`verify-freeze.py` reconstructs the exact baseline bytes by removing the one
new private block, the precise `Mathlib.Tactic.FinCases` import, and the three
appended completion notes, then restoring only the three authorized proof
bodies. Equality with `git show BASE:Loop.lean` proves preservation of every
existing declaration, signature, order, non-target proof, and historical
spec docstring. The script also checks sole-file ownership and that every new
declaration is private. See `freeze-check.log`.

The recorded size exception in this batch brief applies to the final 5713-line
owned file. The growth keeps the track/clear reimplementation and new forwarding
controller private under exclusive file ownership; it does not alter shared
files. Style lint over `TuringMachine/Build` has 0 FAIL and 2 WARN, for the
already size-exempt `Loop.lean` and untouched `Primitives.lean`.

## Pinned environment and recovery disclosure

- Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; all manifest dependency
  sources checked out at their pinned revisions.
- `lake exe cache get` was invoked exactly once. It built the cache executable
  but failed while installing `leantar` because tar could not apply archive
  ownership in this container. This invocation is not reported as successful.
- Recovery used the already extracted pinned `leantar`, then the pinned
  `Cache` API directly. An initial all-mathlib recovery was interrupted; the
  successful recovery used a task-specific cache and the transitive closure of
  the 28 Mathlib imports required by the 57-module tree: 916 cache modules,
  779 missing downloads, all downloaded and unpacked successfully.
- This container hides the process-specific executable link used by Lean's
  runtime to locate its installation. A small `LD_PRELOAD` compatibility shim
  maps only the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`.
  The Lean executable, kernel, mathlib sources, and project definitions were
  not modified. The shim's C source is included as `proc_exe.c` for disclosure.
- No `lake build` was invoked. The 57-module bootstrap was completed in the
  committed order, then the final sweep used a new empty output directory with
  `scripts/lean_check_tree.sh`. Each module requires exit 0, no error diagnostic,
  and a fresh nonempty `.olean`.

The verification logs are from the exact delivered source. Reproduction in a
normal pinned environment needs no shim: use the committed module-order script,
then run `EmitterLAxioms.lean` with that fresh olean tree first on `LEAN_PATH`.
`verify-freeze.py /path/to/repository` checks the diff against the required base.
The archive's `SHA256SUMS` covers every other archive entry.

## New private declarations

All names below are in `Turing.FinTM`; all are private. Generated equation,
recursor, projection, and instance-support constants are covered transitively
by the kernel traversal.

- `emCallIdleTM`
- `emCallEvalTM`
- `emCallEvalCfg`
- `emCall_eval_run`
- `emCall_eval_initial`
- `emCall_eval_first`
- `emCallInterval`
- `emCallCleared`
- `emCall_cleared_step`
- `emCallClearTM`
- `emCallClearCfg`
- `emCall_clear_left`
- `emCall_cleared_zero`
- `emCall_cleared_all`
- `emCall_clear_scan`
- `emCall_origin_erase`
- `emCall_clear_origin`
- `emCall_clear_run`
- `emCallSpan`
- `emCall_span_extend`
- `emCallSlots`
- `emCallTrackTM`
- `emCallTrackCfg`
- `emCallTrackMid`
- `emCall_track_action`
- `emCall_track_stamp`
- `emCallLo`
- `emCallHi`
- `emCall_track_extent`
- `emCall_track_support`
- `emCall_span_zero`
- `emCall_track_initial`
- `emCall_track_run`
- `emCall_track_computes`
- `emCall_span_interval`
- `emCall_track_clearable`
- `emCall_first_entry`
- `emCall_clear_first`
- `emCallRightTM`
- `emCallRightCfg`
- `emCall_right_step`
- `emCall_right_run`
- `emCallRightScan`
- `emCall_right_scan`
- `emCall_right_finish`
- `emCall_right_endpoint`
- `emCall_right_computes`
- `emCall_prepared_eval_first`
- `emCallAction`
- `emCallCfg`
- `emCall_apply`
- `emCall_relocate_run`
- `emCallFinishTM`
- `emCallFinishCfg`
- `emCall_erase_last`
- `emCall_finish_arg`
- `emCall_finish_rewind`
- `emCall_finish_transfer`
- `emCall_finish_erase`
- `emCall_finish_run`
- `emCallSource`
- `emCallState`
- `emCallTripleIndex`
- `emCallTripleSelect`
- `emCall_triple_inverse`
- `emCallPairIndex`
- `emCallPairSelect`
- `emCall_pair_inverse`
- `emCallTM`
- `emCallLayout`
- `emCall_layout_cases`
- `emCall_layout_triple`
- `emCall_layout_pair`
- `emCall_triple_pair`
- `emCall_triple_other`
- `emCall_pair_triple`
- `emCallFrame`
- `emCallBankFrame`
- `emCall_bank_initial`
- `emCall_bank_final`
- `emCall_bank_step`
- `emCall_banks_run`
- `emCall_prepare_initial`
- `emCall_prepare_final`
- `emCall_prepare_run`
- `emCall_finish_initial`
- `emCall_finish_final`
- `emCall_finalize_run`
- `emCall_complete`
- `emCall_exit_fixed`
- `emCall_first`
- `emLoop_step_prefix`
- `emLoop_run_prefix`
- `emLoopHost`
- `emLoopHost_fuel_capture`
- `emLoopHost_init`
- `emLoopHost_input_rewind`
- `emLoopHost_fuel_rewind`
- `emLoopHost_fuel_copy`
- `emLoopHost_fuel_return`
- `emLoopHost_fuel_setup`
- `emLoopHost_prepare`
- `emLoopHost_release`
- `emLoopHost_borrow_step`
- `emLoopHost_borrow_run`
- `emLoopHost_borrow_rewind`
- `emLoopHost_borrow`
- `emLoopHost_reject`
- `emLoopForwardCfg`
- `emLoop_forward_apply`
- `emLoop_forward_run`
- `emLoopCall`
- `emLoopCall_frame`
- `emLoopHost_body_forward`
- `emLoopHost_anchor_return`
- `emLoopCall_empty`
- `emLoopHost_start`
- `emLoopHost_round`
- `emLoop_sum`
