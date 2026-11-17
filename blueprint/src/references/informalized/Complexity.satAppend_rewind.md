<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satAppend_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Work Tape

**Claim.** For $r\le |w|$, starting in the work-rewind state with work tape $w$ and head at $r-1$, the machine reaches the input-rewind state with the same tape and head at zero after $r+1$ steps, leaving the input head unchanged.

**Proof.** Induct on $r$. At $r=0$, the work head is at $-1$, so the work tape reads blank. The rewind-state transition changes to the input-rewind state and leaves the work head at zero; the input head and tape contents are unchanged. The run-length identities express this transition as the required one-step run. For the successor case $r+1$, the bound gives $r<|w|$. Thus at head position $r$, the work tape contains the symbol $w[r]$ and is nonblank (`bufferTape_nat`). The transition moves the work head left, keeps the tape unchanged, and stays in the work-rewind state, yielding the configuration with head at $r-1$. Decomposing the run into this first step and the remaining run (`runFrom_succ_eq_step`), the induction hypothesis applies with parameter $r$ and its bound follows from $r+1\le |w|$. The zero-step run identity is used in the base case (`runFrom_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_zero`.
