<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Input Rewind

**Claim.** From a configuration in the start state, the prescribed left-moving transitions reach the left end and then move right into the destination state, restoring the other configuration fields, in at most the current input-head position plus two steps.

**Proof.** The start-state transition is a control action that moves left, enters the scan state, and leaves work tapes and output unchanged. The control-action application fact gives the resulting configuration explicitly (`Turing.FinTM.controlAction_apply`). Its input-head position is the old position minus one (`Turing.FinTM.moveInputPos_neg_val`), hence is at most the input length. Starting from this scan configuration, the scan rule moves left over each Boolean input symbol; upon reading blank it moves right and enters the destination. The scan lemma says this reaches position one after the scan-position plus one steps, without changing the other fields (`Turing.FinTM.rewind_scan`). Adding the initial step to that scan time, using run addition (`Turing.MultiTapeTM.runFrom_add`), gives the required final configuration. The subtraction formula for the first move bounds the total by the original head position plus two.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`.
