<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Work-Tape Head

**Claim.** For any input $y$, word $u$, valid input-head position $p$, and $j\le |u|$, the comparator starting in rewind state with true flag, work word $u$, work head at $j-1$, and input-head position $p$ reaches comparison state with true flag, the same input position and word, and work head at zero after $j+1$ steps.

**Proof.** Induct on $j$. At $j=0$, the work head is at position $-1$, where the buffer contains no symbol (`bufferTape_left`). The rewind transition therefore advances the work head to zero, leaves the input head and tape unchanged, and enters comparison state. This is the required one step. For the successor case, the head starts at position $j$. Since $j<|u|$, the tape contains the $j$th bit there (`bufferTape_nat`). The rewind transition moves one cell left, leaving state and input position unchanged. Thus the configuration becomes the rewind configuration with head at $j-1$. The induction hypothesis completes the remaining $j+1$ steps; together with the first step this gives the asserted $(j+1)+1$ steps. The step-to-run identity and the zero-time run identity formalize these phase counts (`runFrom_succ_eq_step`, `runFrom_zero`), while a zero input-head movement leaves that position fixed (`moveInputPos_zero`).

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
