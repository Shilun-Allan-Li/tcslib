<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_prepare_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparing the Successor State

**Claim.** Under the stated table decomposition, the prescribed number of steps takes the interpreter from successor decoding to the pending-action phase. The table cursor moves to the end of the unary successor field, the state tape records the successor index (or zero when absent), and the state cursor returns to 1.

**Proof.** Split according to whether a successor state is present. If it is absent, the unary field has length zero, so the table bit at the current cursor is the terminating false marker. The table-read fact (`timedCut_table_read`) identifies this bit; the transition rule then enters the pending-action phase immediately, with the halt flag set and the state tape still encoding zero. The run for one step is expressed using the zero-run and successor-run identities (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`). If a successor state $q$ is present, the current table bit is true, again by `timedCut_table_read`, so the interpreter first enters the state-copying phase. The unary-copy fact (`timedCut_unary_copy`) copies the $q$ unary symbols into the state tape and advances the table cursor past them and their terminating marker, entering the rewind phase. The state-tape marker fact (`universalStateTape_marker`) supplies the false marker at position zero and ensures that the rewind scan stops there. The state-rewind fact (`timedCut_state_rewind`) therefore returns the cursor to 1 and enters the pending-action phase, with the state tape encoding $q$. Finally, split the total duration into the initial transition, the copy segment, and the rewind segment; the run-concatenation identity (`Turing.MultiTapeTM.runFrom_add`) composes these segments. The resulting cursor is $|l|+q+1$, which is the end of the unary field, and the halt flag is false.

**Key facts.** `Turing.timedCut_table_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.timedCut_unary_copy`, `Turing.universalStateTape_marker`, `Turing.timedCut_state_rewind`, `Turing.MultiTapeTM.runFrom_add`.
