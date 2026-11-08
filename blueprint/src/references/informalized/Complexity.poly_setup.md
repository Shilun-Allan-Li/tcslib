<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Setup Rewind

**Claim.** For every $j\le q$, after $j+1$ setup steps from heads at $j-1$, the machine reaches loop level $c$ with all heads at $0$, preserving the tapes and empty output.

**Proof.** Induct on $j$. At $j=0$, the heads are at $-1$, so tape $0$ is blank. The setup transition moves every head one cell right and enters loop level $c$, placing all heads at $0$. For the successor case, the heads begin at $j$, where the unary tape contains a $1$ because $j<q$. The setup transition moves every head one cell left and stays in setup, giving heads at $j-1$. Apply the induction hypothesis to the remaining $j+1$ steps. These transitions do not write on the tapes or emit output, so those parts of the configuration are preserved.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
