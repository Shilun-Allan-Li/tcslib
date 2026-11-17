<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.wret_sweep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output-Tape Return Sweep

**Claim.** For every natural number $j$, starting in state $\mathrm{wret}$ with $j$ leading ones on the output tape and its head at $j-1$, after $j+1$ steps the state is $\mathrm{wdec}$, the tape is unchanged, and the head is at zero.

**Proof.** Induct on $j$, generalizing the remaining word $L$. If $j=0$, the head is at position $-1$, where the buffer tape is blank; the blank-cell return step changes the state to $\mathrm{wdec}$ and advances the head to $0$. The run-of-zero and run-successor identities identify this single step with the claimed run.

For the successor case, the head starts at position $j$. This is within the first $j+1$ entries of the replicated block, so the buffer tape contains a one there (`bufferTape_at` and the list indexing identity). The symbol-return step therefore keeps the state in $\mathrm{wret}$ and moves the head left to $j-1$ (`wret_some`). Rewrite the tape as $j$ leading ones followed by the remaining word with one additional leading one. The induction hypothesis, applied with that enlarged remainder, now completes the remaining $j+1$ steps and puts the head at zero in state $\mathrm{wdec}$. The run-successor identity accounts for the initial step, giving the total of $(j+1)+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.Meyer.wret_none`, `Complexity.Meyer.bufferTape_at`, `Complexity.Meyer.wret_some`, `Turing.MultiTapeTM.runFrom_zero`.
