<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean :: sum_scaled_iid_gaussian_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted sums of independent Gaussians

**Claim.** A finite weighted sum of independent centered Gaussian random variables with common variance $\sigma_0$ is centered Gaussian, with variance $\sigma_0$ times the sum of the squared weights.

**Proof.** First scale each variable by its coefficient. Scaling a centered Gaussian by $x_j$ leaves it centered and multiplies its variance by $x_j^2$ (`map_const_mul_gaussian`). Applying measurable coordinatewise maps preserves independence, so the scaled variables remain independent. Now induct on the finite index set. For the empty set the sum is constantly zero, whose law is the centered Gaussian of variance zero. For an insertion, write the sum as the newly added scaled variable plus the sum over the remaining indices. Independence of the family makes these two summands independent. The sum of independent centered Gaussians is centered Gaussian, with variance the sum of their variances; applying the induction hypothesis gives variance $\sigma_0\sum_j x_j^2$. This establishes the stated law for every finite index set.

**Key facts.** `map_const_mul_gaussian`.
