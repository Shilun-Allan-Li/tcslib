<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Comparator Heads

**Claim.** For four Boolean words with maximum length $m$, starting in the rewind control with all work-tape heads at $j-1$ and running for $j+1$ steps, for any $j\le m$, reaches completed control carrying the same verdict with all heads at zero, while preserving the words, input-head position, and empty output.

**Proof.** Use induction on $j$. When $j=0$, each head is at position $-1$, where the buffer representation reads blank. The rewind transition sees that all four tapes are blank, enters completed control carrying $b$, and moves the heads forward from $-1$ to zero; it leaves the input position and tape contents unchanged. Thus one step gives the required configuration. The zero input-head movement preserves the input position (`Turing.moveInputPos_zero`), and a run of zero steps is the starting configuration (`Turing.MultiTapeTM.runFrom_zero`).

For the successor case, start with heads at $j$. Since $j<m$ follows from the induction hypothesis's bound on $j+1$, at least one word has a symbol at position $j$, by the common-boundary characterization (`Complexity.clCmp_blank`). The aligned-read fact identifies the four symbols seen by the machine (`Complexity.clCmp_read`). The rewind transition therefore stays in rewind control and moves all heads one position left, to $j-1$, leaving the other configuration data unchanged. The remaining $j+1$-step run is exactly the induction hypothesis from that configuration. Runs split into one initial step followed by the remaining steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`), proving the claim.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.clCmp_blank`, `Complexity.clCmp_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
