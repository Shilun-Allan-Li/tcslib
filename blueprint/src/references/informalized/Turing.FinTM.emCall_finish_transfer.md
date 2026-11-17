<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finalizer Transfer Phase

**Claim.** If $c=ur$, then starting in state $3$ with the capture head at $|u|$, the argument head at $|u|$ in install mode or at the origin in emit mode, and the specified contents and output, after $|r|+1$ steps the finalizer reaches state $4$. It has copied or emitted the full capture word as appropriate, and both heads have the stated final positions.

**Proof.** Induct on the remainder $r$. When $r$ is empty, $c=u$, so the capture head is at $|c|$, just beyond the last symbol. It reads blank and the state-$3$ transition advances to state $4$, placing the heads at the required positions; the zero-run and successor-run identities express this as the required one-step run (`runFrom_zero`, `runFrom_succ_eq_step`). For the inductive step, write $r=b r'$. From $c=u b r'$, cell $|u|$ contains $b$ (`bufferTape_nat`). The state-$3$ transition reads this symbol and advances the capture head. In install mode it also writes $b$ at the corresponding argument cell; in emit mode it appends $b$ to the output. The buffer-append identity gives the updated buffer as the old buffer with this last symbol added (`bufferTape_append`), and a zero input movement preserves the input-head position (`moveInputPos_zero`). The resulting configuration is the induction-hypothesis starting configuration with prefix $u b$ and remainder $r'$. The induction hypothesis completes the transfer, and the one transition plus the remaining $|r'|+1$ steps totals $|r|+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.bufferTape_append`, `Turing.moveInputPos_zero`.
