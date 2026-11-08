<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean completion of a halting computation

**Claim.** If the source machine halts with output $y$ after $T$ steps, the clean wrapper reaches the specified restored administrative configuration within $3T+|x|+|y|+8$ steps.

**Proof.** Choose the first halting time $t\le T$. The first-halt principle gives a live run before $t$ and shows that the configuration at $t$ agrees with the one at time $T$, so it has output $y$. The captured-simulation result then identifies the wrapper's state at time $t$ with the logged source configuration and its recorded history. One transition enters the undo phase; the undo-entry fact puts the wrapper into the undo machine on that history. The restoration result reverses the logged work-tape changes in at most $2t+1$ steps and returns the source work fields to their original values, retaining $y$ and placing the capture head at $|y|$. Thus after the initial simulation, entry, and restoration, the wrapper is in administrative state 1 at the source's time-$t$ input position.

Next rewind the input head to position 1. The rewind lemma supplies a run of length $u$ bounded by the current input position plus two, ending in state 3 at position 1. One buffer-action step enters state 4 and moves the capture head from $|y|$ to $|y|-1$. The retained-word rewind result, applied with $j=|y|$, then reaches state 5 with capture head zero in $|y|+1$ steps. A final control transition halts in the requested administrative configuration. The run-addition and successor laws concatenate these phases. Using $t\le T$, the restoration bound, the input-position bound, and the $|y|+1$ rewind cost yields the total bound $3T+|x|+|y|+8$.

**Key facts.** `Complexity.enumCont_first_halt`, `Complexity.enumCont_clean_capture`, `Complexity.enumCont_clean_undo_entry`, `Complexity.enumCont_clean_restore`, `Complexity.enumCont_rewind`, `Complexity.enumCont_buffer_apply`, `Complexity.enumCont_clean_buffer_rewind`, `Turing.FinTM.controlAction_apply`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
