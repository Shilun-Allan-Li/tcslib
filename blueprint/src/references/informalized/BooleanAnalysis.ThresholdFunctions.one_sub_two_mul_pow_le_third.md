<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.one_sub_two_mul_pow_le_third -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Decay Past a Reciprocal Scale

**Claim.** If $\delta\leq 1/2$ and $1<\delta m$, then $(1-2\delta)^m\leq 1/3$.

**Proof.** The assumptions imply $0\leq 1-2\delta$ and $\delta>0$. Bernoulli's inequality gives $(1+2\delta)^m\geq 1+2\delta m$. Also, $0\leq(1-2\delta)(1+2\delta)=1-4\delta^2\leq1$, so raising this product to the $m$th power shows $(1-2\delta)^m(1+2\delta)^m\leq1$. Combining these inequalities, and using $1+2\delta m>3$, yields $(1-2\delta)^m\leq 1/(1+2\delta m)<1/3$, hence the claimed weak bound.
