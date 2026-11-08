<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clReplay_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Rewind of the Replay Machine

**Claim.** For every $j\le |w|$, starting in rewind state with buffer $w$, output $out$, and work-tape head at $j-1$, the replay machine reaches emitting state with head at zero after $j+1$ steps, preserving the other stated configuration data.

**Proof.** Proceed by induction on $j$. For $j=0$, the head is at $-1$ and one rewind-state step moves it to zero and enters the emitting state; the run at zero further steps is the starting configuration (`runFrom_zero`), so the claimed one-step result follows. For the successor case, the induction hypothesis applies to the configuration whose head is at $j-1$. At the current head position $j$, the buffer contains $w[j]$ (`bufferTape_nat` and the list-index identity, valid since $j<|w|$). The rewind transition therefore moves the head one cell left, from $j$ to $j-1$, and keeps the machine in rewind state without changing the buffer, output, or input-head position. Decompose the run into this first step and the remaining $j+1$ steps (`runFrom_succ_eq_step`), then apply the induction hypothesis. The arithmetic identifies the initial head expression $(j+1)-1$ with $j$.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
