<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_live_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Bounded Live Simulation Block

**Claim.** For a coded machine in a present state and a table cursor within its serialization, the interpreter reaches a pending-action configuration in a bounded number of steps, with a valid next table cursor, and its next ordinary step agrees with one machine step.

**Proof.** Fix the current state $q$ and let $a$ be the machine action for its current input and work-tape reads. The serialization split (`timedCut_lookup_parts`) places the relevant record after the header, all earlier state groups, and the earlier records in $q$'s group. The proof follows the interpreter through those portions of the serialization in order.

First, the main control step selects the record index, using the input-reading fact (`universalInput_read`) to ensure the paired input presents the same symbol as the simulated machine. The interpreter-step fact (`timedCut_Eval_step`) gives this first transition. It then rewinds the table cursor to the start (`timedCut_table_rewind`) and counts past the doubled encoding of the number of states (`timedCut_count_run`). The unary initial-state field is skipped next (`timedCut_initial_skip`), leaving the interpreter at the start of the record groups.

The selection lemma (`timedCut_select`) skips the earlier state groups and records and positions the interpreter at the eight action bits for $a$. The fixed-field reading lemma (`timedCut_read_fixed`) reads those bits, and the next-state preparation lemma (`timedCut_prepare_next`) moves past the unary next-state field, arriving in the pending-action phase. The run-joining lemma (`timedCut_run_join`) composes these successive runs into a single run of length $d$.

Finally, the selected record is indeed the transition action $a$, and the serialization shape theorem (`universal_record_shape`) supplies the record-length calculation. These facts bound the accumulated time by $3L+5(N+1)+20$ and show that the resulting cursor $p'$ is at most $L$. The action-application lemma (`timed_apply_record`) identifies the ordinary interpreter's next step from this pending-action configuration with the simulation configuration after applying $a$ to the source machine configuration. Since the source state is present, this is precisely one step of the coded machine.

**Key facts.** `Turing.timedCut_lookup_parts`, `Turing.universalInput_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.timedCut_Eval_step`, `Turing.timedCut_table_rewind`, `Turing.timedCut_count_run`, `Turing.timedCut_initial_skip`, `Turing.timedCut_select`, `Turing.timedCut_read_fixed`, `Turing.timedCut_prepare_next`, `Turing.timedCut_run_join`, `Turing.universal_record_shape`, `Turing.timed_apply_record`.
