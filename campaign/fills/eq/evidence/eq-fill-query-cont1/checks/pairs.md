**Cross-file pairs (20)**, each with an owned-file declaration on one side:

| target | source | share | disposition |
|---|---|---|---|
| `SeamLayout.lean::sl_unarySplit_copy` | `NTimeDiagonalizer.lean::qy_run_one` | 100% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::sl_unarySplitTM_run` | `NTimeDiagonalizer.lean::qy_run_one` | 99% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::sl_pairSkip_two_steps` | `NTimeDiagonalizer.lean::qy_run_one` | 99% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `ExhaustiveReplay.lean::xr_halt_fixed` | `NTimeDiagonalizer.lean::qyC_mapState` | 83% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `Encoding.lean::pairDiag_separator` | `NTimeDiagonalizer.lean::qy_run_one` | 75% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::exists_seamLayoutTM` | `NTimeDiagonalizer.lean::qyC_mapState` | 72% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::splitEmit_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::scanCopy_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::extract_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::emitterToken_separator` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Loop.lean::loopHost_fuel_copy` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::sl_rewrap` | `NTimeDiagonalizer.lean::qyC_mapState` | 70% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `ExhaustiveReplay.lean::xr_phase_step` | `NTimeDiagonalizer.lean::qyC_mapState` | 69% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `NTimeDiagonalizer.lean::qyEmitTM` | `Simulation.lean::emitAction` | 66% | idiom: the model's one-symbol emission action; `FinTM.emitAction` halts at its chain's end, which the emitter's prefix cannot (it continues to its scan), so it is not reusable here |
| `NTimeDiagonalizer.lean::qy_call` | `SeamLayout.lean::sl_rewrap` | 52% | idiom: `seamReleaseTM_runFrom_pos` and the `Cfg.mapState` field equations around a seam (`SeamLayout` is a model to read; no lemma re-derived) |
| `NTimeDiagonalizer.lean::qy_cmp_run` | `Nondeterminism.lean::b2_unary_run` | 50% | idiom: a run lemma's statement shape over a unary tape; a different machine (L2's comparator against `Nondeterminism`'s unary decider) |

**In-file pairs (100)**, each with its justification:

| target | source | share | justification |
|---|---|---|---|
| `QyKit.bCl` | `QyKit.bAbJ` | 95% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_transfer` | `qy_copy` | 94% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_clockHost_finish` | `qy_clock_start` | 91% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `QyKit.bCg` | `QyKit.K` | 90% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyTestS` | `qyTestP` | 89% | two explicit time bounds of the same shape, for different runs |
| `qyRndS` | `qyTestP` | 89% | two explicit time bounds of the same shape, for different runs |
| `QyKit.bCg` | `QyKit.bPb` | 88% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_call` | `qyC_mapState` | 86% | the `Cfg.mapState` field-equation idiom around a seam (`qy_call`'s conversions) |
| `QySpec` | `QyInSpec` | 85% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPb` | `QyKit.bCl` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bCl` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bPr` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCl` | `QyKit.bPr` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bPr` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyRndS` | `qyTestS` | 85% | two explicit time bounds of the same shape, for different runs |
| `QyInSpec` | `QySpec` | 85% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPb` | `QyKit.bAbK` | 84% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyClockSpec` | `QySpec` | 84% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPr` | `QyKit.bAbK` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCl` | `QyKit.bAbK` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bAbK` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bAbJ` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bAb0` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bCg` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPr` | `QyKit.bAbJ` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bAbJ` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPr` | `QyKit.bAb0` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCl` | `QyKit.bAb0` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bAb0` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyTestP` | `qyTestS` | 82% | two explicit time bounds of the same shape, for different runs |
| `QyKit.bCl` | `QyKit.bPb` | 81% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_two_pow_bits_le` | `qy_log_bits` | 81% | `Nat.bits` length facts, each through `qy_log_bits`'s `Nat.log` reading |
| `QyKit.bPr` | `QyKit.bCl` | 80% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAbK` | `QyKit.bPr` | 79% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_unpair_succ_gt` | `qy_unpair_succ_last` | 79% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyKit.bAbJ` | `QyKit.bCl` | 79% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_copy_over` | `qy_copy` | 77% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bCl` | `QyKit.bCg` | 77% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPr` | `QyKit.bPb` | 76% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_transfer` | `qy_clear` | 75% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_not_scratch_ge` | `qy_not_scratch_tp` | 75% | the two off-scratch facts (bank blocks, named tapes): the same case split on the clock's bank |
| `qy_unpair_succ_last` | `qy_unpair_succ_gt` | 75% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `qy_ones_val` | `qy_rung_val` | 74% | the counter values of `1^m` and `0^m 1`, each by induction on `m` |
| `qy_copy_over` | `qy_clear` | 74% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAbK` | `QyKit.bCl` | 74% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_rndS_le` | `qy_rndP_le` | 73% | the stopping and the passed round's bound simplifications: same expansion pattern, different bounds |
| `QyKit.bAbJ` | `QyKit.bPr` | 73% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyTestS` | `qyRndS` | 72% | two explicit time bounds of the same shape, for different runs |
| `qy_mid_run` | `qy_top_run` | 72% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `QyClockSpec` | `QyInSpec` | 72% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPr` | `QyKit.bCg` | 72% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_transfer` | `qy_copy_over` | 71% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAbK` | `QyKit.bPb` | 71% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_copy` | `qy_copy_over` | 71% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_top_run` | `qy_mid_run` | 71% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qy_mid_code` | `qy_top_code` | 70% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qyTestP` | `qyRndS` | 70% | two explicit time bounds of the same shape, for different runs |
| `qy_copy` | `qy_writeConst` | 69% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_setup_long` | `qy_setup_short` | 69% | the long and short paths through the same host: the short one is a prefix of the long one's phases |
| `qy_main_long` | `qy_main_short` | 69% | the long and short paths through the same host: the short one is a prefix of the long one's phases |
| `qy_expandHost` | `qy_expand_start` | 69% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `qy_midB_le` | `qy_topB_le` | 69% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qy_rung_val` | `qy_ones_val` | 68% | the counter values of `1^m` and `0^m 1`, each by induction on `m` |
| `qy_hosted_last` | `qy_hosted'` | 68% | the phase host's segment with and without a final dispatch (`phaseHostTM_run` against `phaseHostTM_run_le`) |
| `qy_transfer` | `qy_writeConst` | 68% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_ledger` | `qy_sum_affine` | 67% | two sums over `Finset.range`, each by `Finset.sum_range_succ` induction |
| `QyKit.bAb0` | `QyKit.bPr` | 67% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAbK` | `QyKit.bCg` | 66% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAbJ` | `QyKit.bPb` | 66% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_copy` | `qy_clear` | 65% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAbK` | `QyKit.bAbJ` | 65% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_hosted'` | `qy_hosted_last` | 64% | the phase host's segment with and without a final dispatch (`phaseHostTM_run` against `phaseHostTM_run_le`) |
| `qy_unpair_succ_lt` | `qy_unpair_succ_last` | 64% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyMPh` | `QyTPh` | 64% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qyAt2_move` | `qy_moveOne` | 63% | head-move equations for the comparator and for one tape |
| `qy_sum_affine` | `qy_ledger` | 63% | two sums over `Finset.range`, each by `Finset.sum_range_succ` induction |
| `qy_rndP_le` | `qy_rndS_le` | 63% | the stopping and the passed round's bound simplifications: same expansion pattern, different bounds |
| `QyKit.bAb0` | `QyKit.bCl` | 63% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_unpair_succ_gt` | `qy_unpair_succ_lt` | 62% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyKit.bAbJ` | `QyKit.bCg` | 61% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_unpair_succ_lt` | `qy_unpair_succ_gt` | 61% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `qy_unpair_succ_last` | `qy_unpair_succ_lt` | 61% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyTPh` | `QyMPh` | 61% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qyMidM` | `qyTopM` | 61% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `QyKit.bAbJ` | `QyKit.bAbK` | 61% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAb0` | `QyKit.bPb` | 60% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_clear` | `qy_copy_over` | 60% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_not_scratch_tp` | `qy_not_scratch_ge` | 58% | the two off-scratch facts (bank blocks, named tapes): the same case split on the clock's bank |
| `qy_clear` | `qy_copy` | 58% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_copy_over` | `qy_writeConst` | 56% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAb0` | `QyKit.bCg` | 56% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_clear` | `qy_writeConst` | 56% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_clock_start` | `qy_expand_start` | 54% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `qy_loop` | `qy_notStop` | 53% | the escape set's membership test (`qyLocE`) read in both |
| `qy_copy` | `qy_transfer` | 53% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_writeConst` | `qy_copy` | 53% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_topB_le` | `qy_midB_le` | 52% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qy_expandHost` | `qy_wordPatch_ones` | 52% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `qy_two_pow_bits_le` | `qy_lt_two_pow_bits` | 51% | `Nat.bits` length facts, each through `qy_log_bits`'s `Nat.log` reading |
| `qy_clockHost_finish` | `qy_expand_start` | 50% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
