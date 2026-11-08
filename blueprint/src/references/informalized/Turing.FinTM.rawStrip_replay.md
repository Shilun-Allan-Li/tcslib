<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replaying the retained word

**Claim.** For every $j\le |a|$, after $j$ steps from state $3$ with $a$ on the work tape, the head at coordinate $0$, and empty output, the machine remains in state $3$, the head is at $j$, and the output is the prefix of $a$ of length $j$.

**Proof.** Induct on $j$. At $j=0$, the initial configuration already has the asserted state, head position, and empty prefix. For the successor case, use the induction hypothesis after $j$ steps. Since $j<|a|$, the head at coordinate $j$ reads the $j$th bit of $a$ (`bufferTape_nat`). The state-$3$ transition emits that bit, advances the work head by one, and leaves the tape, input position, and state unchanged; zero input movement fixes the input position (`moveInputPos_zero`). Thus the output becomes the first $j$ bits followed by the bit at index $j$, which is exactly the prefix of length $j+1$. The run recurrence (`runFrom_succ_eq_step'`) identifies this transition with the next step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
