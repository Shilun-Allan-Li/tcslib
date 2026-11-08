<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.ExpTimeLe.nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Expected-Time Bounds

**Claim.** If every finite partial sum of the probabilities that a randomized computation has not halted is bounded above by $B$, then $B$ is nonnegative.

**Proof.** Use the bound with the empty partial sum, indexed by $K=0$. The sum over no time indices is $0$, so the hypothesis gives $0\le B$.
