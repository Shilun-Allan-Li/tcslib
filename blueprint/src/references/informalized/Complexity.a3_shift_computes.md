<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_shift_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact time for the shift machine

**Claim.** The shift machine halts after $|x|+|w|+2$ steps on input $x$ and outputs $|x|$ false bits followed by $w$.

**Proof.** After $|x|$ scanning steps, the scan invariant gives the scanning state, the input head at the end marker, and exactly $|x|$ false bits in the output (Complexity.a3_shift_scan). Since the input symbol there is blank, the next transition enters the first output-emission state without changing the output. The emission lemma says that, from this state, the machine emits $w$ and halts in $|w|+1$ steps (Turing.FinTM.emit_halts). Splitting the total run into the scan and this final segment gives $|x|+(|w|+1)+1=|x|+|w|+2$ steps, using run addition and the one-step successor identity (Turing.MultiTapeTM.runFrom_add; Turing.MultiTapeTM.runFrom_succ_eq_step'). The endpoint characterization of computation in time then yields the claim (Turing.FinTM.computesInTime_iff).

**Key facts.** `Complexity.a3_shift_scan`, `Turing.FinTM.emit_halts`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
