<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capture Rewind Phase

**Claim.** If $c=uv$, then from state $2$ with the capture head at $|u|-1$, after $|u|+1$ steps the finalizer reaches state $3$ with the capture tape unchanged and its head at the origin. The argument head and empty output remain unchanged.

**Proof.** Induct on $u$ by removing its last letter. If $u$ is empty, the capture head is at $-1$, where the buffer has no symbol, so the state-$2$ transition advances to state $3$ and moves the capture head to the origin. The zero-run and successor-run identities reduce this case to that transition (`runFrom_zero`, `runFrom_succ_eq_step`); the zero input movement leaves the input-head position fixed (`moveInputPos_zero`). For the inductive step, write $u=v b$. Because $c=v b\,\mathrm{suf}$, cell $|v|$ contains $b$ (`bufferTape_nat`). In state $2$, reading this symbol moves the capture head one cell left without modifying either tape or output, leaving the state at $2$. The head position becomes $|v|-1$ and the remaining run length is $|v|+1$, so the induction hypothesis completes the rewind to state $3$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
