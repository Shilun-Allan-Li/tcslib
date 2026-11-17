<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_shift_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Output of the Zero-Prefixing Machine

**Claim.** For any binary words $w,x$, the machine defined using $w$ halts on input $x$ with output consisting of $|x|$ zero bits followed by $w$, after exactly $|x|+|w|+2$ steps.

**Proof.** The scan invariant at time $|x|$ places the machine in its scanning state, with the input head at the right end of the input and output already equal to $|x|$ zero bits (`Complexity.e3_shift_scan`). Since the head is at the end marker, the next transition enters the output phase, leaving that output unchanged. The output-phase halting lemma says that from this state the machine halts in $|w|+1$ further steps and appends $w$ (`Turing.FinTM.emit_halts`). Thus it halts at total time $(|x|+1)+(|w|+1)=|x|+|w|+2$ with the claimed output. The characterization of computation in time identifies these halting and output conditions with the desired computation claim (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Complexity.e3_shift_scan`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.emit_halts`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`.
