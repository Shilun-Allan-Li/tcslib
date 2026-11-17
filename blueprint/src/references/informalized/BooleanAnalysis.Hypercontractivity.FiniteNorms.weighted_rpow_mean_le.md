<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_rpow_mean_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted exponential mean inequality

**Claim.** For a finite set with nonnegative weights of positive total mass, the exponential of the weighted mean of the exponents, multiplied by the total weight, is at most the weighted sum of the exponentials.

**Proof.** The function $t\mapsto\rho^t$ is convex for $\rho>0$. Apply the convexity inequality for a finite weighted center of mass to the values $d_i$ with weights $w_i$. The positive total weight allows division by that mass, yielding $\rho^{(\sum_i w_i d_i)/(\sum_i w_i)}\le (\sum_i w_i\rho^{d_i})/(\sum_i w_i)$. Multiplying by the total weight proves the result.
