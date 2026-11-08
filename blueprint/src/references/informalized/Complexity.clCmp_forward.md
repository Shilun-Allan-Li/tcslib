<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Aligned Forward Scan

**Claim.** For every $j$ at most the maximum word length, running the comparator for $j$ steps from its initial scanning configuration reaches the scanning control after $j$ columns, with all four work-tape heads at position $j$.

**Proof.** Proceed by induction on $j$. At $j=0$, the run has taken no steps, so it is in the initial scanning control and the heads are at zero. For the successor case, assume the claimed configuration after $j$ steps and suppose $j+1$ is at most the maximum word length. Then $j$ is strictly below that maximum, so one comparator step scans the next column and advances each head to $j+1$, updating the control to the state after $j+1$ columns (`Complexity.clCmp_forward_step`). A run of $j+1$ steps is the run of $j$ steps followed by one step (`Turing.MultiTapeTM.runFrom_succ_eq_step'`), which completes the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.clCmp_forward_step`.
