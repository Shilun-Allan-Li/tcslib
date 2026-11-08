<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission Chain

**Claim.** Starting in emission state $j$, after $j+1$ steps the machine is in advance state $0$, with the same head positions and output extended by $j$ ones.

**Proof.** Induct on $j$. When $j=0$, the emission transition at zero goes directly to advance state $0$ and leaves the heads and output unchanged; the run decomposition into one step followed by zero steps gives the result (`runFrom_succ_eq_step`, `runFrom_zero`). For $j+1$, the transition emits one true symbol and moves to emission state $j$. Apply the induction hypothesis to the remaining $j+1$ steps. The resulting output appends one true symbol followed by the $j$ symbols from the induction hypothesis, which is the list of $j+1$ ones; associativity of append and the successor rule for `replicate` identify the output.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
