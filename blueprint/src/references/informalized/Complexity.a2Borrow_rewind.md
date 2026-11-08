<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Borrow_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind to the Tape Origin

**Claim.** For every output word, input word $x$, valid input-head position $p$, binary word $u$, Boolean flag $b$, and integer $j$ with $0\le j\le |u|$, the specified rewind configuration with head at cell $j-1$ reaches the configuration with head at zero, unchanged tape, and the same flag after exactly $j+1$ steps.

**Proof.** Induct on $j$. When $j=0$, the head starts at cell $-1$. The scanned tape cell is blank (`Turing.FinTM.bufferTape_left`), so the rewind state takes its blank-cell transition: it moves the head right to zero and enters the state carrying $b$. This is one step; the input head and output do not change. For the successor case, the starting head is at cell $j$. Because $j<|u|$, the buffer tape there contains the bit $u_j$ (`Turing.FinTM.bufferTape_nat`). In the rewind state, either bit is left untouched while the head moves one cell left and the state remains the same. Thus the first step takes the configuration to the induction hypothesis's starting configuration, with head at $j-1$; the remaining $j+1$ steps finish the rewind. The bound needed by the induction hypothesis follows from $j+1\le |u|$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
