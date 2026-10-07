# E5-closure dedup: kernel-derived live/dead inventory and deletion record

Per the gate's approved disposition (round-1 finding 14) and its adopted
guidance: liveness is kernel reachability from the certified 87-name public
surface of the six owned modules (program: the committed round-3 walker
adapted to reachability; roots = every non-private kernel name), collapsed
to source-declaration cones (a source private is kernel-dead only if its
main constant and every generated descendant are unreachable). A
kernel-dead root cited textually by retained source (comment-stripped scan;
e.g. a simp-set mention that left no kernel trace) is **demoted to kept**
for elaboration safety. Deletion is whole-block, deletion-only, at source
granularity. Snapshot.lean: all four privates live, untouched. No deletion
by prefix or checkpoint label; the guidance's named cases all check out
(`clFill*` live on the producer path; `clCertificateCall`,
`clTrack_schedule` dead and deleted; `e3c_bits_injective` live and kept;
SAT's maximum-pass prefix live).

## `TCSlib/Complexity/ClassNP/Nondeterminism.lean` — 73 deleted, 15 demoted-kept

Deleted (kernel-dead, textually unreferenced):

- `a2Debit_success`
- `e3_coefficient_pos`
- `e3_split_coefficient_zero`
- `e3_split_complete`
- `e3_split_degree_zero`
- `e3_split_empty`
- `e3cClearCfg`
- `e3cClearTM`
- `e3cCleared`
- `e3cCompareCfg`
- `e3cCompareTM`
- `e3cEvalCfg`
- `e3cEvalTM`
- `e3cHi`
- `e3cIdleTM`
- `e3cInterval`
- `e3cLo`
- `e3cRightCfg`
- `e3cRightScan`
- `e3cRightTM`
- `e3cSlots`
- `e3cSpan`
- `e3cSplitEmitCfg`
- `e3cSplitEmitTM`
- `e3cSplitEmit_double`
- `e3cSplitEmit_run`
- `e3cSplitEmit_separator`
- `e3cSplitEmit_suffix`
- `e3cSplitPos`
- `e3cSplitPos_read`
- `e3cSplitPos_succ`
- `e3cTrackCfg`
- `e3cTrackMid`
- `e3cTrackTM`
- `e3c_binary_check`
- `e3c_candidate_envelope`
- `e3c_clear_first`
- `e3c_clear_left`
- `e3c_clear_origin`
- `e3c_clear_run`
- `e3c_clear_scan`
- `e3c_cleared_all`
- `e3c_cleared_step`
- `e3c_cleared_zero`
- `e3c_compare_first`
- `e3c_compare_nonblank`
- `e3c_compare_rewind`
- `e3c_compare_run`
- `e3c_compare_scan`
- `e3c_eval_budget`
- `e3c_eval_first`
- `e3c_eval_initial`
- `e3c_eval_run`
- `e3c_first_entry`
- `e3c_origin_erase`
- `e3c_prepared_eval_first`
- `e3c_right_computes`
- `e3c_right_endpoint`
- `e3c_right_finish`
- `e3c_right_run`
- `e3c_right_scan`
- `e3c_right_step`
- `e3c_span_extend`
- `e3c_span_interval`
- `e3c_span_zero`
- `e3c_track_action`
- `e3c_track_clearable`
- `e3c_track_computes`
- `e3c_track_extent`
- `e3c_track_initial`
- `e3c_track_run`
- `e3c_track_stamp`
- `e3c_track_support`

Demoted to kept (kernel-dead but textually cited by retained source):

- `a3n_prevalidation`
- `b2_tables_coincide`
- `b2_unary_mask`
- `certificateSplit_complete`
- `cont_poly_guess_phase`
- `e3SplitAccept`
- `e3SplitStep`
- `e3_bits_length_bound`
- `e3_find_congr`
- `e3_find_eq`
- `e3_loop_bound`
- `e3_loop_result`
- `e3_split_of_body`
- `e3_step_inv`
- `e3_step_orbit`

## `TCSlib/Complexity/ClassNP/EXP.lean` — 2 deleted, 1 demoted-kept

Deleted (kernel-dead, textually unreferenced):

- `a3_split_unique`
- `enumCont_clean_verifier`

Demoted to kept (kernel-dead but textually cited by retained source):

- `a3_split_empty`

## `TCSlib/Complexity/ClassNP/SAT.lean` — 11 deleted, 0 demoted-kept

Deleted (kernel-dead, textually unreferenced):

- `satChain_sizes`
- `satMeasure`
- `satReduction_size`
- `satSplitClause_sizes`
- `satStreamRound_chunk_bound`
- `satTransformFrom_bounds`
- `sat_clause_serial_bound`
- `sat_measure_decode`
- `sat_measure_serialize`
- `sat_serial_bound`
- `sat_split_even`

## `TCSlib/Complexity/ClassNP/Tautology.lean` — 2 deleted, 0 demoted-kept

Deleted (kernel-dead, textually unreferenced):

- `taut_malformed`
- `taut_verifier_even`

## `TCSlib/Complexity/CookLevin/Hardness.lean` — 65 deleted, 4 demoted-kept

Deleted (kernel-dead, textually unreferenced):

- `CLBounds`
- `clCeiling_pos`
- `clCertificateCall`
- `clClause_cost_le`
- `clCountInc_nondecreasing`
- `clCount_seam`
- `clCounts_halted`
- `clCounts_width_mono`
- `clFlatten_bounds`
- `clGroup_bounds`
- `clHorizon_lower`
- `clHorizon_upper`
- `clInputGroup_bounds`
- `clInputLength_bound`
- `clLastCode_halted`
- `clLastCode_previous`
- `clLastCode_zero`
- `clLiteralCount_le`
- `clLiteral_lt_numVars`
- `clPack_disjoint`
- `clPack_injective`
- `clPack_lt`
- `clPin_bounds`
- `clPins`
- `clPins_length`
- `clPrepHeader_machine`
- `clReadFields_fields`
- `clReadFields_records`
- `clReadFields_row`
- `clRead_first`
- `clRead_idle`
- `clRec_bank`
- `clRec_prefix_silent`
- `clRecordFields`
- `clRecordFields_length`
- `clRecordedHeader_native`
- `clRecords_fields`
- `clRefClock_bound`
- `clRefClock_first`
- `clRefClock_initial`
- `clRefClock_return`
- `clRefClock_run`
- `clRefClock_step`
- `clRefCount_frame`
- `clRefTM`
- `clRef_admin`
- `clRef_initial`
- `clRef_run`
- `clRef_schedule`
- `clSchedule_compare`
- `clSerializeClause_length`
- `clSerializeLit_length`
- `clSerialize_length`
- `clSerialize_length_le`
- `clSerialize_uniform`
- `clSignedWords`
- `clSigned_compare`
- `clTableauGroups_bounds`
- `clTableauGroups_length`
- `clTableau_length`
- `clTableau_quadratic`
- `clTemplate_wiring`
- `clTrack_schedule`
- `clVisitRow_cleanCall`
- `clWorkGroup_bounds`

Demoted to kept (kernel-dead but textually cited by retained source):

- `clCount_first`
- `clRefClockTM`
- `clRefCountTM`
- `clRefCount_first`

**Totals: 153 source privates deleted; 20 kernel-dead roots kept on textual grounds.**
