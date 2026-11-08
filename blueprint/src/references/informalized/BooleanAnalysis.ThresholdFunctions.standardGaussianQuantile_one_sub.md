<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_one_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Gaussian Quantiles

**Claim.** For every real number $a$ with $0<a<1$, the standard Gaussian quantiles satisfy $Q(1-a)=-Q(a)$.

**Proof.** The quantile identity gives $\Phi(Q(a))=a$ for $0<a<1$ (`standardGaussianCDF_quantile`). Gaussian symmetry of the CDF says $\Phi(-x)=1-\Phi(x)$ (`standardGaussianCDF_neg`), so substituting $x=Q(a)$ yields $\Phi(-Q(a))=1-a$. Applying quantile recovery to this CDF value shows that $Q(1-a)=-Q(a)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_neg`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_eq`.
