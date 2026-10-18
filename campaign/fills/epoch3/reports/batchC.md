# Epoch 3, Batch C — COMPLETE

`Complexity.oblivious_of_mem_DTIME` is proved. The completed binary simulator is oblivious on all inputs of each length and decides the supplied language within the required uniform quadratic bound. The final 25-module sweep exits 0 with zero errors and exactly the three permitted external sorry warnings. The target's axioms are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This completed archive supersedes the earlier partial checkpoint. The previously missing initialization, operational data-sweep, padded source-run, and final-output invariants are now proved and connected to the target theorem.

## Repository and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested upstream branch: `complexity/arora-barak-ch1`.
- Specification: `briefs/epoch3-batchC.md` on that branch.
- Pinned base: `71721842a2336d5562ef831a19b0e86e063dddaa`.
- Working branch: `fill/epoch3-C`.
- Final local commit: `e4876115254ca04c2ab39e59f4395754e2c15bd5` — `Complete the oblivious simulator correctness proof`.
- The patch series includes the recovered component checkpoint `0e941d3d5d00032a730a7221bbe3464b7967ef2a`, followed by the completion commit above. The final tree is the verified deliverable.
- Only modified repository file: `TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean`.
- No push or pull request.

The frozen `Oblivious` definition, target theorem header, original audited five-step sketch, and `set_option` headers were compared against the pinned base and preserved. `TimeConstructible` and every unowned file are unchanged. No other sorry was touched; no admission or axiom was added. Every explicit new declaration is private, above the target, and listed below.

The required policy, plan section 5, corrected sketch, phase-2 finding 2 and reaudit, and epoch-2 finding-9 obligations were read. The original sketch remains intact, followed by a flagged implementation appendix.

## Completion checklist

- [x] Target filled with a kernel-checked proof.
- [x] Full masked-clock lockstep: `maskedClock_lockstep`.
- [x] Explicit length-only schedule and trajectory invariant at every physical time.
- [x] Concrete copy, park, allocation, data-sweep, source-state, and output invariants.
- [x] Exactly the prescribed macrostep budget, including idle sweeps after early source halting.
- [x] Own fixed-duration binary coding with an exact trajectory proof.
- [x] Obliviousness for all same-length inputs, including empty input and different decision outcomes.
- [x] Actual quadratic cost ledger connected to `DecidesInTime`.
- [x] All private declarations, requested shared lemmas, size escalation, and docstring appendix recorded.
- [x] Full 25-module sweep passes, zero `error:` lines, exactly the three permitted external sorries.
- [x] Target axiom audit excludes `sorryAx`.
- [x] Owned-file-only diff; patch application, bundle, and archive checks pass.

## Construction and proof certificates

### Masked clock

`maskedClock` replaces every nonblank input read by the fixed symbol and preserves blanks. `maskedCfg` changes the dependent input to the constant word while preserving the numerical input position, state, all work tapes and heads, and output. `maskedClock_step` and `maskedClock_lockstep` prove full-configuration correspondence at every time. Thus the witness's trajectories and halting time depend only on input length. `maskedClock_computes` retains its specification, and `clockStageCfg_run` / `clockStageCfg_captures` connect the actual schedule to that masked computation, including every emitted budget bit and a possible final emission.

### Schedule and trajectory invariant

`obliviousSchedule` implements the clock, reset, input copy, budget conversion, guide allocation, all fixed sweeps, and final halt. Its non-clock input tests distinguish only blank from nonblank. `obliviousSchedule_oblivious` proves its length-only trajectory without assumptions on source computations or logical input validity.

`decorateTM` adds data tapes and finite data registers. Its transition takes movements and the successor/halting decision exclusively from the schedule; data determines writes, finite registers, and output. `scheduleCfg`, `decorateTM_step`, and `decorateTM_run` give the exact projection onto the silent schedule. `decorateTM_heads` proves that each added head follows its designated schedule head. `decorateTM_oblivious` therefore gives the trajectory invariant at every time, including after halting. `decoratedCfg_step` exposes the exact local data update while retaining that schedule.

### Binary coding at every physical time

`parallelTM` encodes each logical cell as a transverse fixed-width binary block on synchronized tracks. Its tape count is finite and independent of input length. Every logical read/write is one physical transition; there are no variable-duration intermediate coding states. `parallelTM_step` and `parallelTM_run` prove exact configuration correspondence, and `parallelTM_oblivious` proves every physical head trajectory. `parallelTM_computes` preserves the completed embedded-bit output at the same time. Neither the existential `alphabet_reduction` witness nor `one_work_tape` is used as an obliviousness result.

### Input copy and first macrostep

`setupCfg_reset` handles an arbitrary clock endpoint, including either blank boundary and empty input. `setupCfg_copy` proves the fixed copy schedule and parks the native input head at its right blank; all subsequent actions have zero native input movement. `setupCfg_initializes` proves exact budget conversion and guide allocation.

`copiedPayload`, `copyDataWrite_left`, and `copyDataWrite_next` prove the actual copied input and both boundary tags. `copiedPayload_full` identifies the result with the initial source configuration. `prepCondition` / `prepInvariant` track the data across every initialization phase; `prepInvariant_step` and `prepInvariant_run` prove the invariant on actual decorated runs. The unique unary origin forces entry at counter position one. Later macrosteps increment that counter, so they cannot satisfy the first-macrostep clause again. `obliviousSchedule_ready` and `dataTM_ready` connect the exact schedule endpoint to blank source work tapes, the complete virtual input, the source initial state, and an empty output stream.

### Operational macrostep and idling

Virtual tapes are represented relative to their heads, all located at the guide origin. The origin transition selects the source action, performs its work-tape writes, and saves the last output bit. The forward scan caches left neighbors; the backward scan selects left/current/right payloads to implement each virtual head movement. Native input clamping is represented by boundary tags.

`dataCfg_forward_prefix` and `dataCfg_backward_prefix` prove these properties for actual decorated scan prefixes. `dataCfg_sweeps` composes the physical scans and turns. `dataCfg_written`, `sourcePayload_apply`, and `obliviousSourceMove_correct` relate them to the native source action, including explicit blank writes and clamped input moves. `sourcePayload_support` places the old and next initialized source configurations inside the radius-`3B` guide. `dataCfg_simulates` then proves one complete macrostep, with exact duration, successor state, represented tapes, and saved answer.

An absent source state selects `obliviousSourceAction_idle` and `obliviousSourceMove_idle`: no source writes, output, or virtual movement. The independent physical schedule continues. `dataCfg_iterates` proves the correspondence for all `B` macrosteps, including every idle macrostep after early source halting. `macroCfg_repeat` / `macroCfg_finish` give the same exact schedule count independently of source behavior.

### Final bit and deadline

`dataCfg_finish` emits exactly one saved bit and halts on the final counter test. `sourceAnswer_at_budget` identifies that register with the source decider's answer, since `B >= a*T(n)`. `dataTM_computes` composes initialization, all padded macrosteps, and the final test, with no earlier output. `parallelTM_computes` transfers this result to the binary candidate.

`obliviousCandidate_halts` independently establishes the concrete quadratic deadline. `obliviousCandidate_decides` uses uniqueness of a deterministic machine's completed output to combine that deadline with the complete output certificate. The target selects the source machine and clock witness supplied by `hL` and `hT` and returns this same candidate and its explicit constant.

The trajectory theorem has no source-halting or decision premise: it covers every pair of binary inputs of the same length, including empty inputs and pairs with opposite answers. The computation proof also quantifies over every binary input; it makes no nonempty-input assumption.

## Cost ledger

Let `n` be the input length, `U = T(n)`, `a` the source-decider multiplier, `b` the clock multiplier, `tau` the masked clock's first halting time, and `w` the captured word width. Set `B = (a+1)(U+1)` and guide radius `R = 3B`. The proof uses `n <= U`, `tau <= b(U+1)`, and `w <= b(U+1)`.

| Stage | Exact schedule cost | Main certificate |
| --- | --- | --- |
| Initialize sentinels and capture clock | `1 + tau` | `clockStageCfg_run`, `clockStageCfg_captures` |
| Reset native input | `p-1+2`, natural truncated subtraction; at most `n+2` | `setupCfg_reset` |
| Copy input and return guide | `2n+4` | `setupCfg_copy` |
| Fixed-width budget conversion | `(U+1)(2w+(a+1)+4)` | `setupCfg_budget_round`, `setupCfg_budget_all` |
| Allocate guide and position counter | `14B+10` | `setupCfg_allocation` |
| Each complete macrostep | `6R+8` | `macroCfg_cycle`, `dataCfg_simulates` |
| All `B` macrosteps | `18B^2+8B` | `macroCfg_repeat`, `dataCfg_iterates` |
| Final counter test, single output, halt | `1` | `macroCfg_finish`, `dataCfg_finish` |
| Binary coding | One physical step per logical step | `parallelTM_run` |

The total is at most

`tau + 3n + 18 + (U+1)(2w+(a+1)+4) + 22B + 18B^2`.

`obliviousLedger_bound` bounds this by

`(18(a+1)^2 + 23(a+1) + 3b + 25)(U+1)^2`.

The theorem uses the explicit constant `c = 18(a+1)^2 + 23(a+1) + 3b + 25`. This is a bound on the actual initialized binary simulator, now connected to correct decision output.

## Verification and archive integrity

Toolchain: pinned Lean 4.25.0. The existing toolchain/cache checkpoint was reused; `lake exe cache get` was invoked once over the task. No `lake build` was run. All checks use the prescribed `scripts/lean_check_tree.sh` gate. After completing the source, the full command was run from the beginning:

```sh
( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )
```

`final-sweep.log` records exit 0, all 25 ordered modules, zero `error:` lines, and exactly three remaining sorry warnings. The strengthened script requires a fresh output object for each successful module. Other nonfatal linter warnings remain; there are no target admissions.

| Remaining declaration | Warning location | Brief status |
| --- | --- | --- |
| `exists_effectiveMachineCode` | `Encoding.lean:455` | Permitted |
| `universal` | `Universal.lean:102` | Permitted |
| `timed_universal` | `Universal.lean:165` | Permitted |

After the sweep, a scratch audit file imported the checked module and ran `#print axioms Complexity.oblivious_of_mem_DTIME`. `axioms.log` records:

```text
'Complexity.oblivious_of_mem_DTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`. A source-level audit also finds no `sorry`, `admit`, or new `axiom` declaration in the owned file. The frozen statement, definition, audited sketch, and header options were checked against the pinned base; `git diff --check` passes.

`epoch3-C.patch` was generated by `git format-patch 71721842 --stdout`. Applying the entire series to the pinned source reproduces the delivered source byte for byte. `epoch3-C.bundle` verifies and carries `refs/heads/fill/epoch3-C` at the final commit, with the pinned base as prerequisite. `SHA256SUMS` covers the six other archive files and excludes itself. The zip contains exactly the seven requested files.

## Requested shared lemmas

The following generic tools remain private copies because this batch owns only one source file: constant-input masking and full lockstep; schedule decoration with exact projection and aligned-head preservation; transverse finite-alphabet coding with step-exact trajectories; exact one-lane transduction; unchanged-word zipper-frontier identities; and the explicit decorated-configuration step identity. They are candidates for later shared refactoring after review. No shared module was modified or split.

## Escalations and docstring appendix

- **File size:** `Oblivious.lean` has 4086 lines, exceeding the approximately 1000-line threshold. As the brief directs, this is recorded here instead of splitting the proof or changing an unowned module. The complete construction has 238 private source declarations.
- **Representation choices:** binary blocks occupy synchronized transverse tracks. Virtual heads stay at the common guide origin and their tape contents shift during the data sweeps. These choices use the statement's unrestricted finite work-tape count. No one-work-tape or two-tape normal form is claimed.
- **Implementation appendix:** the preserved audited sketch is followed by `Implementation notes — Epoch 3, Batch C`, describing the representation, preparation invariant, operational source simulation, final bit, and explicit constant. All new declarations have docstrings; substantial proofs include local proof sketches.
- **Unresolved proof obligations:** none. The earlier missing global correctness proof is complete. No statement weakening or alternative result was substituted.

## All new private declarations

All 238 explicit private source declarations are listed below in source order, with final source line numbers. They live in namespace `Complexity`. Inductive entries also account for their generated constructors, recursors, and instances; generated elaborator auxiliaries are not separately listed. No new public declaration was introduced.

| Line | Kind | Private name |
| ---: | --- | --- |
| 86 | def | `maskedCfg` |
| 93 | lemma | `maskedCfg_input` |
| 101 | lemma | `maskedCfg_apply` |
| 115 | def | `maskedClock` |
| 122 | lemma | `maskedClock_step` |
| 141 | lemma | `maskedClock_lockstep` |
| 151 | lemma | `maskedClock_oblivious` |
| 166 | lemma | `inputInsensitive_oblivious` |
| 178 | lemma | `maskedClock_computes` |
| 191 | def | `decorateTM` |
| 209 | def | `scheduleCfg` |
| 216 | lemma | `decorateTM_step` |
| 249 | lemma | `decorateTM_run` |
| 266 | lemma | `decorateTM_heads` |
| 294 | lemma | `decorateTM_oblivious` |
| 319 | def | `parallelCode` |
| 338 | def | `parallelDecode` |
| 342 | lemma | `parallelDecode_code` |
| 347 | def | `parallelBit` |
| 351 | lemma | `parallelBit_embed` |
| 357 | def | `parallelTM` |
| 372 | def | `parallelCfg` |
| 384 | lemma | `parallelCfg_input` |
| 392 | lemma | `parallelCfg_read` |
| 407 | lemma | `parallelTM_step` |
| 442 | lemma | `parallelCfg_init` |
| 453 | lemma | `parallelTM_run` |
| 465 | lemma | `parallelTM_oblivious` |
| 476 | lemma | `parallelTM_computes` |
| 491 | inductive | `OblSymbol` |
| 501 | def | `oblEmbed` |
| 504 | def | `clockBit` |
| 510 | inductive | `OblPhase` |
| 542 | def | `oblAction` |
| 549 | def | `nextThird` |
| 561 | def | `obliviousSchedule` |
| 666 | lemma | `obliviousSchedule_output` |
| 676 | lemma | `obliviousSchedule_oblivious` |
| 685 | abbrev | `OblPayload` |
| 688 | def | `blankPayload` |
| 691 | def | `dataCell` |
| 697 | abbrev | `OblData` |
| 702 | def | `obliviousSourceAction` |
| 711 | def | `obliviousSourceMove` |
| 721 | def | `obliviousDataInit` |
| 730 | def | `obliviousVisit` |
| 781 | def | `obliviousCandidate` |
| 790 | lemma | `obliviousCandidate_oblivious` |
| 800 | lemma | `obliviousSourceAction_idle` |
| 805 | lemma | `obliviousSourceMove_idle` |
| 814 | def | `budgetValue` |
| 819 | lemma | `budgetValue_bits` |
| 828 | def | `budgetBorrow` |
| 835 | lemma | `budgetBorrow_false` |
| 841 | lemma | `budgetBorrow_length` |
| 848 | lemma | `budgetBorrow_underflow` |
| 859 | lemma | `budgetBorrow_value` |
| 876 | def | `laneCfg` |
| 884 | def | `laneAction` |
| 889 | lemma | `laneCfg_read` |
| 896 | lemma | `laneCfg_right` |
| 922 | lemma | `lane_run` |
| 951 | def | `budgetVisit` |
| 954 | lemma | `budgetFold` |
| 961 | lemma | `oblAction_budget` |
| 989 | lemma | `obliviousSchedule_borrow` |
| 1002 | lemma | `obliviousSchedule_borrow_run` |
| 1016 | def | `inputPayload` |
| 1020 | def | `inputTag` |
| 1026 | lemma | `inputPayload_head` |
| 1036 | def | `clippedMove` |
| 1040 | lemma | `clippedMove_correct` |
| 1062 | def | `sourcePayload` |
| 1068 | def | `sourceReads` |
| 1073 | lemma | `sourcePayload_origin` |
| 1081 | def | `sourceTotalAction` |
| 1088 | lemma | `obliviousSourceAction_correct` |
| 1096 | lemma | `sourceTotalAction_apply` |
| 1110 | def | `sourceShift` |
| 1116 | lemma | `obliviousSourceMove_correct` |
| 1133 | def | `sourceWrittenPayload` |
| 1148 | lemma | `sourcePayload_apply` |
| 1170 | def | `payloadRow` |
| 1175 | def | `payloadForward` |
| 1182 | def | `payloadBackward` |
| 1189 | lemma | `payloadForward_row` |
| 1193 | lemma | `payloadBackward_row` |
| 1203 | def | `payloadZone` |
| 1209 | lemma | `payloadZone_length` |
| 1218 | lemma | `payloadForward_zone` |
| 1233 | lemma | `payloadBackward_zone` |
| 1246 | lemma | `payload_sweeps_source` |
| 1261 | lemma | `inputPayload_outside` |
| 1283 | lemma | `sourcePayload_support` |
| 1305 | lemma | `lastOutput_append` |
| 1310 | lemma | `sourceAnswer_at_budget` |
| 1321 | def | `clockTape` |
| 1325 | lemma | `clockTape_nil` |
| 1330 | lemma | `clockTape_append` |
| 1345 | def | `clockStageCfg` |
| 1355 | lemma | `clockStageCfg_input` |
| 1363 | lemma | `clockStageCfg_work` |
| 1372 | lemma | `clockStageCfg_step` |
| 1417 | lemma | `finThree_cases` |
| 1427 | lemma | `clockStageCfg_init` |
| 1452 | lemma | `clockStageCfg_run` |
| 1470 | lemma | `clockStageCfg_captures` |
| 1493 | def | `guideTape` |
| 1500 | lemma | `guideTape_left` |
| 1506 | lemma | `guideTape_right` |
| 1512 | lemma | `guideTape_origin` |
| 1519 | def | `macroCfg` |
| 1528 | lemma | `macroCfg_unary` |
| 1536 | lemma | `macroCfg_guide` |
| 1544 | lemma | `macroCfg_apply` |
| 1563 | lemma | `macroCfg_check` |
| 1573 | lemma | `macroCfg_seek` |
| 1584 | lemma | `macroCfg_forward` |
| 1595 | lemma | `macroCfg_backward` |
| 1606 | lemma | `macroCfg_center` |
| 1617 | lemma | `macroCfg_seek_run` |
| 1631 | lemma | `macroCfg_forward_run` |
| 1645 | lemma | `macroCfg_backward_run` |
| 1659 | lemma | `macroCfg_center_run` |
| 1679 | lemma | `macroCfg_cycle` |
| 1725 | lemma | `macroCfg_repeat` |
| 1743 | lemma | `macroCfg_finish` |
| 1757 | def | `setupCfg` |
| 1768 | def | `setupWrite` |
| 1773 | lemma | `setupCfg_apply` |
| 1798 | lemma | `setupCfg_input` |
| 1809 | lemma | `setupCfg_reads` |
| 1820 | lemma | `setupCfg_reset_scan` |
| 1851 | lemma | `setupCfg_reset` |
| 1882 | def | `copyGuide` |
| 1887 | lemma | `copyGuide_next` |
| 1899 | lemma | `copyGuide_origin` |
| 1906 | def | `copyPhase` |
| 1910 | lemma | `setupCfg_copy_left` |
| 1936 | lemma | `setupCfg_copy_prefix` |
| 1970 | lemma | `setupCfg_copy_end` |
| 1995 | lemma | `setupCfg_copy_return` |
| 2027 | def | `unaryTape` |
| 2031 | lemma | `unaryTape_next` |
| 2042 | lemma | `clockTape_origin` |
| 2050 | lemma | `clockTape_end` |
| 2055 | lemma | `setupCfg_budget_back` |
| 2080 | lemma | `setupCfg_budget_start` |
| 2099 | lemma | `setupCfg_append_prefix` |
| 2119 | lemma | `setupCfg_append` |
| 2134 | lemma | `sweepTape_shift` |
| 2156 | lemma | `clockTape_zipper` |
| 2175 | lemma | `clockTape_zipper_end` |
| 2184 | lemma | `laneCfg_setup` |
| 2217 | lemma | `setupCfg_borrow` |
| 2237 | lemma | `setupCfg_borrow_end` |
| 2254 | lemma | `setupCfg_budget_round` |
| 2274 | lemma | `setupCfg_budget_all` |
| 2314 | lemma | `unaryTape_origin` |
| 2319 | lemma | `unaryTape_unit` |
| 2323 | lemma | `unaryTape_end` |
| 2327 | def | `unaryRewindPhase` |
| 2332 | lemma | `setupCfg_unary_rewind` |
| 2361 | lemma | `setupCfg_unary_start` |
| 2378 | def | `guideMark` |
| 2382 | def | `guideFill` |
| 2387 | lemma | `guideFill_zero` |
| 2393 | lemma | `guideFill_origin` |
| 2400 | lemma | `guideFill_next` |
| 2415 | def | `layoutPhase` |
| 2419 | def | `layoutMove` |
| 2422 | lemma | `setupCfg_layout_step` |
| 2445 | lemma | `setupCfg_layout_fill` |
| 2462 | lemma | `nextThird_mod` |
| 2471 | lemma | `setupCfg_layout_prefix` |
| 2494 | lemma | `setupCfg_layout_end` |
| 2512 | def | `rightGuide` |
| 2517 | lemma | `guideFill_right_copy` |
| 2524 | lemma | `rightGuide_origin` |
| 2532 | lemma | `guideFill_left_finish` |
| 2543 | lemma | `setupCfg_right_edge` |
| 2556 | lemma | `setupCfg_layout_return_step` |
| 2573 | lemma | `setupCfg_layout_return_prefix` |
| 2597 | lemma | `setupCfg_layout_return` |
| 2615 | lemma | `setupCfg_layout_right` |
| 2635 | lemma | `setupCfg_layout_left` |
| 2662 | lemma | `setupCfg_start_center` |
| 2689 | lemma | `setupCfg_allocation` |
| 2716 | lemma | `setupCfg_copy` |
| 2731 | lemma | `clockTape_unary_zero` |
| 2737 | lemma | `clockStageCfg_setup` |
| 2757 | lemma | `macroCfg_setup` |
| 2775 | lemma | `setupCfg_finish` |
| 2791 | lemma | `setupCfg_initializes` |
| 2816 | lemma | `obliviousLedger_bound` |
| 2851 | lemma | `obliviousSchedule_halts` |
| 2904 | lemma | `obliviousCandidate_halts` |
| 2924 | def | `decoratedCfg` |
| 2931 | lemma | `decoratedCfg_init` |
| 2949 | lemma | `decoratedCfg_step` |
| 2990 | def | `dataTM` |
| 2996 | def | `dataCfg` |
| 3004 | lemma | `dataCfg_step` |
| 3021 | lemma | `dataCfg_forward_step` |
| 3037 | lemma | `dataCfg_forward_turn` |
| 3053 | lemma | `dataCfg_backward_step` |
| 3073 | lemma | `dataCfg_backward_turn` |
| 3090 | lemma | `dataCfg_forward_prefix` |
| 3141 | lemma | `dataCfg_backward_prefix` |
| 3211 | lemma | `dataCfg_seek_run` |
| 3243 | lemma | `dataCfg_center_run` |
| 3274 | lemma | `dataCfg_check` |
| 3296 | lemma | `dataCfg_written` |
| 3326 | lemma | `dataCfg_sweeps` |
| 3368 | lemma | `sourceWrittenPayload_away` |
| 3382 | lemma | `dataCfg_simulates` |
| 3440 | def | `copiedPayload` |
| 3447 | lemma | `copiedPayload_full` |
| 3459 | def | `copyDataWrite` |
| 3465 | lemma | `copyDataWrite_left` |
| 3480 | lemma | `copyDataWrite_next` |
| 3499 | def | `initialContent` |
| 3506 | def | `prepCondition` |
| 3529 | def | `prepInvariant` |
| 3537 | lemma | `inputSymbol_blank` |
| 3545 | lemma | `copy_input_read` |
| 3558 | lemma | `copy_input_payload` |
| 3572 | lemma | `prepInvariant_action` |
| 3586 | lemma | `unaryOrigin_update` |
| 3602 | lemma | `prepInvariant_step` |
| 3805 | lemma | `prepInvariant_run` |
| 3847 | lemma | `macroCfg_self` |
| 3866 | lemma | `obliviousSchedule_ready` |
| 3898 | lemma | `dataTM_ready` |
| 3933 | lemma | `dataCfg_iterates` |
| 3971 | lemma | `dataCfg_finish` |
| 3986 | lemma | `dataTM_computes` |
| 4011 | lemma | `obliviousCandidate_decides` |
