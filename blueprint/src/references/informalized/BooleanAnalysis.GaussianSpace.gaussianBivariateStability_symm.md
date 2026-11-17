<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Bivariate Stability

**Claim.** If $-1\le\rho\le1$, then Gaussian bivariate stability is symmetric in its two thresholds: $B_\rho(\alpha,\beta)=B_\rho(\beta,\alpha)$.

**Proof.** Use the Gaussian-measure-preserving reflection $R(x,y)=(\rho x+\sqrt{1-\rho^2}\,y,\sqrt{1-\rho^2}\,x-\rho y)$ (\texttt{BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianReflection}). The bound on $\rho$ ensures the square root is real. A direct calculation using $\rho^2+(1-\rho^2)=1$ shows that applying the correlated linear form to $R(x,y)$ recovers $x$. Consequently, the preimage under $R$ of the event with thresholds $(\beta,\alpha)$ is exactly the event with thresholds $(\alpha,\beta)$, with the two inequalities merely exchanged. Since $R$ preserves product Gaussian measure, these events have equal measure. The event is measurable because the Gaussian CDF is continuous (\texttt{BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF}), so measure preservation applies.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianReflection`, `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF`.
