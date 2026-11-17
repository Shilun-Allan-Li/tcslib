<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrVal_replicate_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After False Digits

**Claim.** Placing $j$ false digits before a Boolean list $r$ gives binary value $2^j$ times the value of $r$.

**Proof.** Induct on $j$. For zero false digits the list is just $r$, and the formula holds since $2^0=1$. For the inductive step, prepend one false digit. By the defining recurrence for the list value, this doubles the value of the remaining list. The induction hypothesis supplies the factor $2^j$, so the result is $2\cdot 2^j$ times the value of $r$, namely $2^{j+1}$ times that value.
