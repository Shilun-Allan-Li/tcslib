<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/SparseSampling.lean :: BooleanAnalysis.ThresholdFunctions.sparse_param -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample size exponent bound

**Claim.** If $n,s$ are nonnegative integers, $L,\delta>0$, and $4nL^2/\delta^2\le s$, then $2n\le s(\delta/L)^2/2$.

**Proof.** Multiplying the assumed inequality by the positive number $\delta^2$ gives $4nL^2\le s\delta^2$. As $L^2>0$, divide by $2L^2$ to obtain $2n\le s\delta^2/(2L^2)$. The right-hand side is exactly $s(\delta/L)^2/2$.
