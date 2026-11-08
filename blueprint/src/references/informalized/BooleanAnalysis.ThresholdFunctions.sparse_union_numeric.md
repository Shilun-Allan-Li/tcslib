<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/SparseSampling.lean :: BooleanAnalysis.ThresholdFunctions.sparse_union_numeric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration sum below one

**Claim.** For positive integer $n$, nonnegative integer $s$, and positive $L,\delta$, if $4nL^2/\delta^2\le s$, then $2^n\bigl(2e^{-s(\delta/L)^2/2}\bigr)<1$.

**Proof.** The sample-size hypothesis gives $2n\le s(\delta/L)^2/2$. Negating reverses this inequality, and monotonicity of the exponential yields $\exp(-s(\delta/L)^2/2)\le e^{-2n}$. Thus the expression in question is at most $2^{n+1}e^{-2n}$. This is strictly less than $1$ by the exponential bound for positive dimension.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.sparse_param`, `BooleanAnalysis.ThresholdFunctions.sparse_numeric`.
