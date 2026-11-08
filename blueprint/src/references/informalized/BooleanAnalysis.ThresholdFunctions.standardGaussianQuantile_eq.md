<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of a Quantile

**Claim.** If $\Phi(t)=\alpha$, then the standard Gaussian quantile satisfies $Q(\alpha)=t$.

**Proof.** By strict increase of $\Phi$, the condition $\alpha\leq\Phi(s)$ is equivalent, using $\Phi(t)=\alpha$, to $t\leq s$. Thus the set whose infimum defines $Q(\alpha)$ is exactly the upper ray $[t,\infty)$. Its infimum is $t$, proving the claim.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`.
