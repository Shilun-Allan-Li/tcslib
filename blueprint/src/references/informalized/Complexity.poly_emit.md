<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Emission Chain

**Claim.** Starting in state $\mathrm{emit}_j$, after $j+1$ steps the machine reaches $\mathrm{advance}_0$, preserving the tapes and head positions and appending $j$ ones to the output.

**Proof.** Induct on $j$. When $j=0$, the transition from $\mathrm{emit}_0$ enters $\mathrm{advance}_0$ without emitting a symbol or changing the heads or tapes, which is the claim for zero appended ones. For $j+1$, the transition from $\mathrm{emit}_{j+1}$ emits one $1$ and enters $\mathrm{emit}_j$, leaving the tapes and heads unchanged. The run decomposition separates this first step from the remaining $j+1$ steps. Apply the induction hypothesis with the output already extended by one $1$; associativity of concatenation and the successor rule for list replication identify the result as the original output followed by $j+1$ ones.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
