# Bounded explicit-step census at d64

The four full source captures contain 91 raw explicit `MultiTapeTM.step` tokens: Hardness 58, EXP 33, ExhaustiveReplay 0, InputCall 0. EXP line 593 is a continued `simp only` argument; a same-line closing-form search sees only 90. These are occurrences, not declarations or copies. This is a bounded token/source inspection, not a global absence or retirement claim.

All remaining sites retain review status. In particular EXP `enumCont_absorb` line2000 is another stationary same-kind candidate using an existing live-state premise and `controlAction_apply`; this packet does not modify or execute it. Root owns any scope expansion. The generic live/halted reader applies to the primitive step reading; the surrounding machine-specific transition, frame, simulation or action proof may need further published readings. No new `step_eq` is proposed.

| Category | Occurrences |
| --- | ---: |
| machine-specific-operational-transition-candidate | 51 |
| canonical-live-read-inside-composite-proof | 7 |
| selected-stationary-root | 12 |
| composite-simulation-frame-step-candidate | 13 |
| canonical-halted-read-inside-operational-proof | 7 |
| stationary-general-helper-candidate | 1 |

| File | Line | Declaration | Closing form | State/candidate disposition |
| --- | ---: | --- | --- | --- |
| Hardness.lean | 689 | `clFill_run` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 702 | `clFill_run` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 848 | `clRef_apply` | simp | canonical-live-read-inside-composite-proof |
| Hardness.lean | 976 | `clCount_carry_step` | unfold | machine-specific-operational-transition-candidate |
| Hardness.lean | 1036 | `clCount_rewind` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 1046 | `clCount_rewind` | unfold | machine-specific-operational-transition-candidate |
| Hardness.lean | 1080 | `clCount_idle` | simp | selected-stationary-root |
| Hardness.lean | 1159 | `clBank_step` | unfold | composite-simulation-frame-step-candidate |
| Hardness.lean | 1168 | `clBank_step` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 1171 | `clBank_step` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 1174 | `clBank_step` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 1231 | `clBank_idle` | unfold | selected-stationary-root |
| Hardness.lean | 1304 | `clMoves_correct` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 1306 | `clMoves_correct` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 1434 | `clLeft_until` | simp | canonical-halted-read-inside-operational-proof |
| Hardness.lean | 1441 | `clLeft_until` | unfold | composite-simulation-frame-step-candidate |
| Hardness.lean | 1479 | `clTrack_dispatch` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 1664 | `clCopy_rewind` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 1666 | `clCopy_rewind` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 1703 | `clCopy_idle` | unfold | selected-stationary-root |
| Hardness.lean | 2124 | `clRow_idle` | unfold | selected-stationary-root |
| Hardness.lean | 2412 | `clRec_copy` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 2546 | `clPlaced_release` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 2599 | `clRec_advance` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 2963 | `clCmp_idle` | unfold | selected-stationary-root |
| Hardness.lean | 3098 | `clRead_pair` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3099 | `clRead_pair` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3100 | `clRead_pair` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3156 | `clRead_separator` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3157 | `clRead_separator` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3158 | `clRead_separator` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3181 | `clRead_rewind` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3315 | `clWipe_forward` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3346 | `clWipe_backward` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3348 | `clWipe_backward` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3350 | `clWipe_backward` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3382 | `clWipe_idle` | unfold | selected-stationary-root |
| Hardness.lean | 3426 | `clFresh_idle` | unfold | selected-stationary-root |
| Hardness.lean | 3641 | `clLoad_idle` | unfold | selected-stationary-root |
| Hardness.lean | 3737 | `clInput_backward` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3770 | `clInput_run` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 3782 | `clInput_idle` | unfold | selected-stationary-root |
| Hardness.lean | 3883 | `clPrepare_idle` | unfold | selected-stationary-root |
| Hardness.lean | 4640 | `clReplay_back` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 4671 | `clReplay_forward` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 4695 | `clReplay_run` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 4753 | `clOutput_compute` | unfold | machine-specific-operational-transition-candidate |
| Hardness.lean | 4847 | `clPrepared_idle` | unfold | selected-stationary-root |
| Hardness.lean | 4991 | `clRecord_idle` | unfold | selected-stationary-root |
| Hardness.lean | 5182 | `clReplay_from` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 5216 | `clOutputAt_compute` | unfold | machine-specific-operational-transition-candidate |
| Hardness.lean | 5717 | `clRepeat_round` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 6130 | `clA5Pad_run` | simp | canonical-halted-read-inside-operational-proof |
| Hardness.lean | 6136 | `clA5Pad_run` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 6181 | `clA5Stop_step` | simp | composite-simulation-frame-step-candidate |
| Hardness.lean | 6225 | `clA5Stop_clean` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 6642 | `clA5Map_run` | simp | machine-specific-operational-transition-candidate |
| Hardness.lean | 6652 | `clA5Map_run` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 583 | `enumCont_log_run` | simp | canonical-halted-read-inside-operational-proof |
| EXP.lean | 589 | `enumCont_log_run` | simp | canonical-live-read-inside-composite-proof |
| EXP.lean | 593 | `enumCont_log_run` | continued simp only | canonical-live-read-inside-composite-proof |
| EXP.lean | 795 | `enumCont_undo_run` | simp | canonical-live-read-inside-composite-proof |
| EXP.lean | 904 | `enumCont_clean_undo_entry` | simp | canonical-live-read-inside-composite-proof |
| EXP.lean | 985 | `enumCont_rewind` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1012 | `enumCont_clean_buffer_rewind` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1027 | `enumCont_clean_buffer_rewind` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1134 | `enumCont_concat_native` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1149 | `enumCont_concat_native` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1176 | `enumCont_concat_candidate` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1190 | `enumCont_concat_candidate` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 1321 | `enumCont_return_run` | simp | composite-simulation-frame-step-candidate |
| EXP.lean | 1363 | `enumCont_pad_run` | simp | canonical-halted-read-inside-operational-proof |
| EXP.lean | 1372 | `enumCont_pad_run` | simp | canonical-live-read-inside-composite-proof |
| EXP.lean | 1844 | `enumCont_body_accept` | simp | machine-specific-operational-transition-candidate |
| EXP.lean | 2000 | `enumCont_absorb` | simp | stationary-general-helper-candidate |
| EXP.lean | 2022 | `enumCont_agree_run` | simp | canonical-halted-read-inside-operational-proof |
| EXP.lean | 2025 | `enumCont_agree_run` | simp | canonical-live-read-inside-composite-proof |
| EXP.lean | 2570 | `a3_shift_scan` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 2608 | `a3_shift_computes` | simp | machine-specific-operational-transition-candidate |
| EXP.lean | 2715 | `a3_copy_step` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 2758 | `a3_load_rewind` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 2774 | `a3_load_rewind` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 2803 | `a3_run_start` | unfold | machine-specific-operational-transition-candidate |
| EXP.lean | 2835 | `a3_run_guarded` | simp | canonical-halted-read-inside-operational-proof |
| EXP.lean | 2838 | `a3_run_guarded` | simp | composite-simulation-frame-step-candidate |
| EXP.lean | 2861 | `a3_run_call` | simp | machine-specific-operational-transition-candidate |
| EXP.lean | 2889 | `a3_run_singleton` | simp | machine-specific-operational-transition-candidate |
| EXP.lean | 2953 | `a3_nonempty_run` | simp | canonical-halted-read-inside-operational-proof |
| EXP.lean | 2955 | `a3_nonempty_run` | simp | composite-simulation-frame-step-candidate |
| EXP.lean | 2962 | `a3_nonempty_nil` | simp | machine-specific-operational-transition-candidate |
| EXP.lean | 2974 | `a3_nonempty_computes` | simp | machine-specific-operational-transition-candidate |
