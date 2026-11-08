# Bounded backwards-live inspection of the eight actual FH owners

Actual source: `e0b7fd50ca81d9b8f3dd486f120292da1b4fb880`. Candidate enumeration plus inspection; no global absence or exhaustive-search claim. The original 22 narrower candidates, expanded 39 complete chunks and all 380 raw closing-form hits are retained uncapped. All 39 complete chunks were inspected. Only candidates 24, 28 and 34 match the generic backwards-live reproof kind and need the three private repoints.

| ID | Declaration | Disposition | Inspection |
|---|---|---|---|
| 1 | `Complexity.enumCont_undo_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Undo simulation induction consumes the supplied complete live-prefix guard; it does not infer earlier liveness from a later live endpoint. |
| 2 | `Complexity.enumCont_clean_capture` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Capture simulation consumes the supplied complete live-prefix guard through capture_run. |
| 3 | `Complexity.enumCont_clean_restore` | DIFFERENT_CONTRACT_OR_NO_REPROOF | First-halt/capture restoration uses enumCont_first_halt; this is not generic backwards propagation of liveness. |
| 4 | `Complexity.enumCont_return_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Return simulation induction consumes a supplied complete live-prefix guard. |
| 5 | `Complexity.cont_guess_step` | DIFFERENT_CONTRACT_OR_NO_REPROOF | One-step nondeterministic/deterministic capture correspondence, with a halted-state case split; no two-time liveness inference. |
| 6 | `Complexity.b2_unary_first` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Uses canonical first-halt existence and transfer; deterministic first-None selection, not backwards-live reproof. |
| 7 | `Complexity.b2_guess_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Nondeterministic host simulation shifts a supplied live-prefix guard with runFrom_succ. |
| 8 | `Complexity.b2_guess_coverage` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Coverage proof consumes its supplied full live-prefix guard and previously proved coverage facts. |
| 9 | `Complexity.b2_verify_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Verifier host simulation shifts a supplied live-prefix guard with runFrom_succ. |
| 10 | `Complexity.b2_host_contract` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Host composition consumes provided live-prefix and coverage facts; no generic earlier-live derivation. |
| 11 | `Complexity.sat_first_halt` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Canonical first-halt/output packaging. |
| 12 | `Complexity.sat_call_first_halt` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Canonical first-halt reader plus positive-time packaging from initial liveness. |
| 13 | `Complexity.sat_live_prefix` | ALREADY_READER | Already directly cites MultiTapeTM.runFrom_state_ne_none_of_le. |
| 14 | `Complexity.clRef_apply` | DIFFERENT_CONTRACT_OR_NO_REPROOF | One-source-step/frame correspondence with source-state case split; no time-prefix liveness conclusion. |
| 15 | `Complexity.clMoves_correct` | DIFFERENT_CONTRACT_OR_NO_REPROOF | One-step position correspondence with halted-state stationarity. |
| 16 | `Complexity.clA5_call_first_halt` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Canonical first-halt reader plus positive-time packaging from initial liveness. |
| 17 | `Complexity.clA5_live_prefix` | ALREADY_READER | Already directly cites MultiTapeTM.runFrom_state_ne_none_of_le. |
| 18 | `Turing.MultiTapeTM.ConfigCount.core_injOn` | DIFFERENT_CONTRACT_OR_NO_REPROOF | First-halt minimality and periodic-core injection argument; the supplied later endpoint is halted, not live. |
| 19 | `Turing.FinTM.ComputesInTime.of_spaceUsed_le` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Canonical first-halt minimum and resource count, with forward post-halt stability; different contract. |
| 20 | `Turing.FinTM.ComputesInTime.spaceUsed_le_of_halt` | DIFFERENT_CONTRACT_OR_NO_REPROOF | All-times space bound from a halted endpoint using forward tail absorption, not a backwards-live conclusion. |
| 21 | `Complexity.TimeHierarchy.kCfg_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Lockstep induction from a provided complete live-prefix guard. |
| 22 | `Turing.universal` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Machine-specific simulation blocks and halted-state stuttering, not generic earlier-live inference. |
| 23 | `Turing.timedCut_live_block` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Constructs a ready state and lookup block by machine-specific simulation; no generic two-time live inference. |
| 24 | `Turing.timedCut_live_before` | MECHANICAL_REPAIR | MATCH BLIVE1: decomposes s <= t, uses runFrom_add/runFrom_of_halt contradiction; exact public reader specialization passes. |
| 25 | `Turing.timedCut_no_record` | ALREADY_READER | Consumes local timedCut_live_before, then reasons about the machine-specific applyRecord stop state; wrapper is repointed by BLIVE1. |
| 26 | `Turing.timed_replay` | ALREADY_READER | Consumes timedCut_live_before and no_record to prove lockstep replay; wrapper is repointed by BLIVE1. |
| 27 | `Turing.timedPrefix_penultimate` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Constructs the exact later live endpoint from parser runs; that witness is the premise used by BLIVE2. |
| 28 | `Turing.timedPrefix_live` | MECHANICAL_REPAIR | MATCH BLIVE2: predecessor endpoint plus add/post-halt contradiction; exact public reader and timedPrefix_penultimate specialization passes. |
| 29 | `Turing.timed_interpret_finishes` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Countdown/simulation composition and forward post-halt simplification; consumes timed_replay, not a generic earlier-live reproof. |
| 30 | `Turing.timedCapture_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Capture induction consumes a supplied complete source live-prefix guard. |
| 31 | `Turing.timedFrame_step` | DIFFERENT_CONTRACT_OR_NO_REPROOF | One-step frame correspondence with a halted-state stuttering case. |
| 32 | `Turing.timed_universal` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Non-computation of every output implies live at the same deadline; no earlier-time conclusion. |
| 33 | `Turing.timed_universal_concrete` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Same-deadline non-computation-to-live reasoning; no earlier-time conclusion. |
| 34 | `Turing.universal_live_before` | MECHANICAL_REPAIR | MATCH BLIVE3: decomposes s <= t, uses runFrom_add/runFrom_of_halt contradiction; exact public reader specialization passes. |
| 35 | `Turing.universalPrefix_live` | ALREADY_READER | Already consumes universal_live_before with universalPrefix_penultimate; wrapper is repointed by BLIVE3. |
| 36 | `Turing.universalCapture_run` | DIFFERENT_CONTRACT_OR_NO_REPROOF | Capture induction consumes a supplied complete source live-prefix guard. |
| 37 | `Complexity.enumCont_first_halt` | ALREADY_READER | Already exact canonical exists_first_halt reader, not backwards-live reproof. |
| 38 | `Complexity.SatClean` | DIFFERENT_CONTRACT_OR_NO_REPROOF | A definition specifying a clean/first-halt contract, with no proof. |
| 39 | `Complexity.CLA5Clean` | DIFFERENT_CONTRACT_OR_NO_REPROOF | A definition specifying a clean/first-halt contract, with no proof. |
