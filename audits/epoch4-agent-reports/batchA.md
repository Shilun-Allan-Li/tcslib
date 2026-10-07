# Epoch 4, Batch A — final timed-universal fill

## Result and checklist

`Turing.timed_universal` is proved with the frozen public statement and its full
docstring sketch unchanged. The construction is a finite binary multitape machine.
The final 34-module sweep exits 0 with zero errors and zero sorry warnings.

- [x] Target filled; `sorryAx` absent from the target and all three regression prints.
- [x] All five binding obligations discharged below.
- [x] Explicit startup, transition, output, and quadratic cost ledger recorded.
- [x] Inclusive deadline and deadline-zero boundaries proved.
- [x] Every explicit new private declaration listed; shared-lemma requests and escalation recorded.
- [x] Full 34-module sweep and four axiom prints included.
- [x] Repository diff touches only `TCSlib/Complexity/TuringMachine/Universal.lean`.
- [x] No infrastructure source modified, no push, and no PR.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`  
Source branch: `complexity/arora-barak-ch1`  
Pinned base: `ff2161e491faf61ce42c60a23f02a80c62e33c83`  
Local work branch: `fill/epoch4-A`  
Delivered commit: `6ed6cdd8dfe54a7592f35210ae425a7738849eed`

The existing `universal` and `universal_quadratic` statements, docstrings, and proof
bodies are byte-for-byte unchanged. The sole new import is
`Mathlib.Tactic.FinCases`; all original option headers are retained. The original
module text is retained; a flagged epoch-4 implementation note introduces the new
private construction. No public declaration was added.

## Construction and the five binding obligations

| Obligation | Implementation and proof |
| --- | --- |
| 1. Separate clock and code; canonize only `α` | `timed_input_layout` identifies four copies of each clock bit, the four-cell inner separator, and then `pairEncode α x`. `timedPrefix_clock`, `timedPrefix_code`, and `timedPrefix_complete` show the clock is stored while the parser emits exactly `α`. `timedCanonTM`, `timedCanon_run`, and `timedCanon_complete` run `c.canonizer` on virtual input `α`, preserving both clock and physical suffix position. |
| 2. Buffer source emissions | `timedAction` suppresses native output and appends an emission on lane 5. `timedLift`, `timedAction_apply`, `timed_regular_step`, and `timed_execute` identify that lane with the source output, while actual output stays empty. `timed_interpret_finishes` uses the at-most-one emission per source step, obtained from `MultiTapeTM.step_output`, to pay for buffer length; this is the stepwise form of `MultiTapeTM.output_length_le`. Only `timed_flush` emits success and buffered data; `timed_clock_timeout` emits exactly `[false]`. |
| 3. Decrement once per source transition | `timedBorrow_value` proves a successful fixed-width borrow subtracts exactly one, and `timedBorrow_length` preserves the width. `timed_clock_success` performs that borrow and exactly one pending source action. `timed_interpret_finishes` inducts on the remaining numeric budget, using `timedValue_bits` to initialize it. `timed_bits_length` bounds width by `t`, including zero. |
| 4. Intercept source halting | `timedCut_live_block` reaches a live pending-action checkpoint before application; `timed_replay` transports the lookup through the timed wrapper. `timedAction` maps a native halted successor to live state `emitStart`, capturing even the last transition's emission. `timed_execute` proves that translation, and `timed_flush` supplies the later real halt. |
| 5. Zero and inclusive boundaries | `timedPrefix_complete` parses all separators even for the empty clock word. `timedBorrow_underflow` and `timed_clock_timeout` identify zero credit. In `timed_interpret_finishes`, source halting is inspected before credit is tested: a transition consuming the final credit reaches the halted branch and flushes. The theorem's final proof identifies this answer with source state/output after exactly `t` absorbing steps. |

The stopped controller is proof infrastructure for reaching the selected record;
it is not the delivered machine's halting behavior. Its administrative proofs are
private copies adapted to the stopped transition function. The delivered machine
is `timedUniversalTM`, with six active interpreter lanes: table, state, simulated
work, virtual-input boundary marker, clock, and output buffer. Its finite control
contains the selected eight action bits while it services the clock.

The input suffix `x` is never scanned during startup. The inherited virtual-input
boundary machinery remains in use, with the outer payload `pairEncode (Nat.bits t) α`
as the prefix parameter. `timed_initialized` proves the physical head position and
all initial checkpoint fields; `timedFrame_run` lifts every subsequent inner step
through the inactive canonizer work tapes.

## Realized cost ledger

Fix the scheme and code, and write:

- `M = c.decode α`, `A = α.length`, `L = M.serialize.length`;
- `N = M.numStates + 1`, `q = M.tm.q₀.val`;
- `h = (Nat.bits M.numStates).length`, `K = c.canonizerTime A`;
- `w = (Nat.bits t).length`, with `w ≤ t` by `timed_bits_length`.

| Phase | Transition bound | Proof |
| --- | --- | --- |
| Parse outer clock and code | exactly `4w + 2A + 6` | `timedPrefix_complete` |
| Prepare virtual canonizer input | `A + 2` additional | `timedCanon_start` |
| Canonizer on `α` | at most `K` | `timedCanon_complete` |
| Capture-to-interpreter transfer | at most one additional step after first canonizer halt | `timedCapture_start` |
| Table rewind and source initialization | exactly `L + 2h + 2q + 7` | `timedCut_Interpreter_initialize`, `timed_replay` |
| One stopped lookup | at most `B = 3L + 5N + 20` | `timedCut_live_block` |
| Successful decrement plus source application/buffering | exactly `2w + 4` | `timed_clock_success` |
| Zero-credit check and timeout tag after lookup | exactly `2w + 3` | `timed_clock_timeout` |
| Success tag, buffer rewind/flush, and native halt | exactly `2ℓ + 3` for buffer length `ℓ` | `timed_flush` |

Thus startup is at most `4w + S`, where the implemented code-only term is

```
S = timedStartupBound c α = 3A + K + L + 2h + 2q + 16.
B = universalBlockBound c α = 3L + 5N + 20.
```

Capture and buffering are performed in the same physical transitions as the
wrapped machine's actions. A successful source step therefore costs at most
`B + 2w + 4`. The proof tracks the output-length increase (at most one) directly.
For any checkpoint with remaining credit `r` and existing output length `ℓ`,
`timed_interpret_finishes` gives the combined interpretation/output bound

```
(B + 2w + 8) * (r + 1) + 2ℓ.
```

This includes the final flush or the possible final unsuccessful lookup and
underflow check. From the initialized source, `r = t` and `ℓ = 0`. At most `t`
successful borrows and one zero-credit sweep occur, so countdown work is at most
`(2w + 4) * (t + 1)`.

`timed_cost_bound` and `timed_computes` assemble

```
4w + S + (B + 2w + 8) * (t + 1)
    ≤ (S + B + 14) * (t + 1)^2.
C = S + B + 14.
```

Every term in `C` depends only on `α` and the already fixed scheme `c`. In particular,
`K` is the canonizer time on `α`; neither the clock bits nor `x` enter `C`.

## Boundary behavior

After a positive-budget step, the induction recurses on the actual successor
configuration and the decremented clock. Its first case checks whether that
successor is halted. Consequently, first halting on transition `t` succeeds even
though the remaining credit is zero. The final action's emission is captured
before the success tag and buffer are flushed. Earlier source halting also
succeeds, using absorbing halting to identify the result at time `t`.

At `t = 0`, `Nat.bits 0 = []` but both pairs' separators remain. Startup still
parses their total six cells and canonizes `α`. The initialized source has a live
state, so the zero-credit branch performs a stopped lookup, detects underflow
without applying the selected source action, and emits exactly `[false]`. The
real output buffer has never emitted, so a later timeout likewise discards every
previously captured source emission.

## Requested shared lemmas

No shared-file changes were made. The following future generalizations could
remove local duplication; the current proof is complete without them:

1. Parameterize the interpreter's administrative initialization and lookup proofs
   by a controller agreeing with `universalInterpreter` outside `applyRecord`, or
   export their execution trace up to the pending action. Private copies are the
   `timedCut_*` administrative and lookup family plus `timed_apply_record`.
   The existing final-checkpoint block alone does not expose the point at which
   the wrapper must borrow and intercept halting. Copies also avoid assuming
   separately minted match auxiliaries are syntactically the same.
2. Generalize the capture wrapper to retain an active lane from the original
   machine's work block. The private `timedCapture*` and `timedFrame*` families
   retain the clock; the audited wrapper's interpreter uses a fresh block.
3. Export a reusable one-lane fold/sweep run lemma with arbitrary inactive tapes.
   The private `timed_laneCfg`, `timed_laneAction`, `timed_laneCfg_read`,
   `timed_laneCfg_right`, and `timed_lane_run` are local versions of the pattern
   used in `Robustness/ObliviousCandidate.lean`.

## Escalations and environment deviations

**File-size escalation:** `Universal.lean` is now 2831 lines, exceeding
policy's approximate 1000-line split threshold. The binding brief explicitly
requires all new helpers to remain private in this single owned file and forbids
splitting or editing the three infrastructure modules. Accordingly, this report
records the escalation; no unauthorized split was made. Roughly the first 1100
new lines adapt stopped-interpreter administrative/lookup proofs. The shared
lemma generalizations above describe possible future factoring. There is no
statement obstruction or unproved proof obligation.

Lean was initially unavailable. The Lean 4.25.0 toolchain was installed using
elan; archive extraction required `TAR_OPTIONS=--no-same-owner` to avoid archive
ownership errors. `lake exe cache get` was run once, with that recovery setting,
and fetched/unpacked all 7506 cache files. Two calls to the compiled cache
executable's `unpack` operation were used while completing cache setup. No
`lake build` was run. All proof checks used the per-module checker or the
explicit axiom-print file.

## Verification evidence

`final-sweep.log` contains the full required sweep, with shell tracing to identify
all module invocations:

```sh
( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )
```

The 34 traced module paths equal the 34-line order file exactly, in order. Sweep
exit status: **0**. Every module produced its fresh `.olean`. Counts:
`error:` **0**; `declaration uses 'sorry'` **0**. Other existing/style linter
warnings remain and are visible in the complete log; they are not suppressed.

`axioms.log` was produced by Lean 4.25.0 using the fresh sweep object tree and:

```lean
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.Uncomputability.Halting
#print axioms Turing.timed_universal
#print axioms Turing.universal
#print axioms Turing.universal_quadratic
#print axioms Complexity.HALT_not_computable
```

All four prints are exactly `[propext, Classical.choice, Quot.sound]`; none uses
`sorryAx`. Axiom-print exit status: **0**. The three regression declarations remain
clean. A byte comparison against the base confirms the frozen target statement
and docstring and the two existing universal-theorem proof bodies are unchanged.
`git diff --check` passes, and the base-to-delivery changed-path set contains only
the owned source file.

## Archive and reproduction

The archive contains this report, the modified source at its repository path,
`epoch4-A.patch`, `epoch4-A.bundle`, `final-sweep.log`, `axioms.log`, and
`SHA256SUMS`. The patch is the exact output of
`git format-patch ff2161e4 --stdout`. The bundle contains `fill/epoch4-A` with the
pinned base as its prerequisite; `git bundle verify` passes. Apply the patch with
`git am` at the pinned base, or fetch the work branch from the bundle into a
repository containing that base. No push or PR was performed. `SHA256SUMS` covers
every delivered member except itself.

## New private declarations

All 130 explicit new declarations below are private and in `Universal.lean`.
The two finite-control inductives additionally generate their usual constructors,
recursors, equation/match auxiliaries, and `DecidableEq`/`Fintype` instances; no
handwritten public instances or axioms were introduced. `TimedPrefixControl` has
constructors `clockFirst`, `clockSecond`, `clockThird`, `clockFourth`, `clockEnd`,
`codeFirst`, and `codeSecond`. `TimedControl` has constructors `work`, `clockBack`,
`borrow`, `execute`, `emitStart`, `emitBack`, and `flush`.

- `timedCutInterpreter` (def)
- `timedCut_Eval_reads` (lemma)
- `timedCut_Admin_apply` (lemma)
- `timedCut_Eval_step` (lemma)
- `timedCut_table_read` (lemma)
- `timedCut_table_rewind` (lemma)
- `timedCut_count_run` (lemma)
- `timedCut_StateTape_append` (lemma)
- `timedCut_StateTape_end` (lemma)
- `timedCut_state_rewind` (lemma)
- `timedCut_initial_skip` (lemma)
- `timedCut_unary_copy` (lemma)
- `timedCut_install_marker` (lemma)
- `timedCut_InterpreterInitial` (def)
- `timedCut_InterpreterBase` (def)
- `timedCut_Interpreter_first` (lemma)
- `timedCut_Interpreter_initialize` (lemma)
- `timedCut_skip_fixed` (lemma)
- `timedCut_skip_unary` (lemma)
- `timedCut_skip_record` (lemma)
- `timedCut_skip_records` (lemma)
- `timedCut_skip_groups` (lemma)
- `timedCut_read_fixed` (lemma)
- `timedCut_NextCost` (def)
- `timedCut_prepare_next` (lemma)
- `timedCut_Actions` (def)
- `timedCut_Actions_lookup` (lemma)
- `timedCut_Header` (def)
- `timedCut_serialization_actions` (lemma)
- `timedCut_lookup_parts` (lemma)
- `timedCut_ActionBits_decode` (lemma)
- `timedCut_select` (lemma)
- `timedCut_run_join` (lemma)
- `timed_apply_record` (lemma)
- `timedCut_live_block` (lemma)
- `timedClockPrefix` (def)
- `timed_input_layout` (lemma)
- `timedClockPrefix_length` (lemma)
- `TimedPrefixControl` (inductive)
- `timedPrefixTM` (def)
- `timedPrefixCfg` (def)
- `timed_input_length` (lemma)
- `timed_clock_get` (lemma)
- `timed_clock_separator` (lemma)
- `timedPrefix_advance` (lemma)
- `timedPrefix_write` (lemma)
- `timedPrefix_clock` (lemma)
- `timedPrefix_clock_end` (lemma)
- `timed_code_get` (lemma)
- `timed_pair_get` (lemma)
- `timed_pair_separator` (lemma)
- `timedPrefix_code` (lemma)
- `timedPrefix_complete` (lemma)
- `timedValue` (def)
- `timedValue_bits` (lemma)
- `timedBorrow` (def)
- `timedBorrow_false` (lemma)
- `timedBorrow_length` (lemma)
- `timedBorrow_underflow` (lemma)
- `timedBorrow_value` (lemma)
- `TimedControl` (inductive)
- `timedSix` (def)
- `timedAction` (def)
- `timedAdmin` (def)
- `timedInterpreter` (def)
- `timedLift` (def)
- `timedCut_regular` (lemma)
- `timedCut_live_before` (lemma)
- `timedCut_no_record` (lemma)
- `timedSix_core` (lemma)
- `timedAction_apply` (lemma)
- `timed_regular_step` (lemma)
- `timed_replay` (lemma)
- `timed_laneCfg` (def)
- `timed_laneAction` (def)
- `timed_laneCfg_read` (lemma)
- `timed_laneCfg_right` (lemma)
- `timed_lane_run` (lemma)
- `timedAdmin_clock` (lemma)
- `timedBorrow_fold` (lemma)
- `timed_borrow_run` (lemma)
- `timed_sweep_shift` (lemma)
- `timed_buffer_zipper` (lemma)
- `timed_buffer_zipper_end` (lemma)
- `timedClockCfg` (def)
- `timedClock_step` (lemma)
- `timed_clock_back` (lemma)
- `timed_clock_borrow` (lemma)
- `timed_clock_start` (lemma)
- `timed_clock_pass` (lemma)
- `timed_execute` (lemma)
- `timed_clock_success` (lemma)
- `timed_clock_timeout` (lemma)
- `timedOutputCfg` (def)
- `timed_output_step` (lemma)
- `timed_output_back` (lemma)
- `timed_output_forward` (lemma)
- `timed_flush` (lemma)
- `timedPrefix_penultimate` (lemma)
- `timedPrefix_live` (lemma)
- `timedCanonTM` (def)
- `timedCanonClock` (def)
- `timedCanon_start` (lemma)
- `timedCanon_run` (lemma)
- `timedCanon_complete` (lemma)
- `timedAnswer` (def)
- `timed_interpret_finishes` (lemma)
- `timed_bits_length` (lemma)
- `timedFive` (def)
- `timedFrameAction` (def)
- `timedCaptureTM` (def)
- `timedCaptureCfg` (def)
- `timedCapture_init` (lemma)
- `timedCapture_step` (lemma)
- `timedCapture_run` (lemma)
- `timedCapturedCfg` (def)
- `timedCapture_transfer` (lemma)
- `timedCapture_start` (lemma)
- `timedFrame` (def)
- `timedFrame_reads` (lemma)
- `timedFrame_apply` (lemma)
- `timedFrame_step` (lemma)
- `timedFrame_run` (lemma)
- `timedCaptured_frame` (lemma)
- `timedUniversalTM` (def)
- `timedStartupBound` (def)
- `timed_header_bound` (lemma)
- `timed_initialized` (lemma)
- `timed_cost_bound` (lemma)
- `timed_computes` (lemma)
