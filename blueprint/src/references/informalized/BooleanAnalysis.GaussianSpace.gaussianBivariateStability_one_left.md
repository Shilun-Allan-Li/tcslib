<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_one_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Left Threshold

**Claim.** If $-1\le\rho\le1$ and $0\le\beta\le1$, then $B_\rho(1,\beta)=\beta$.

**Proof.** Because the Gaussian CDF is strictly less than one at every real input, the condition $\Phi(x)\le1$ is automatic. The event defining the bivariate stability therefore reduces to the event that the scalar Gaussian expression $\rho x+\sqrt{1-\rho^2}\,y$ has CDF at most $\beta$. The map sending $(x,y)$ to this expression preserves the standard Gaussian law when $-1\le\rho\le1$ (\texttt{BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianEndpoint}). The measure of its CDF sublevel event is exactly $\beta$ for $\beta\in[0,1]$ (\texttt{BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_comp_le}), proving the identity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one`, `BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianEndpoint`, `BooleanAnalysis.GaussianSpace.measureReal_standardGaussianCDF_comp_le`.
