<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.abs_gaussianBivariateStability_sub_right_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-Threshold Lipschitz Bound

**Claim.** For $\rho\in[-1,1]$ and $\beta,\beta'\in[0,1]$, with any real first threshold $\alpha$, the absolute difference between the Gaussian bivariate stabilities at $(\alpha,\beta)$ and $(\alpha,\beta')$ is at most $|\beta-\beta'|$.

**Proof.** Regard the second linear combination, $\rho Z_1+\sqrt{1-\rho^2}Z_2$, as a coordinate whose distribution is standard Gaussian. The endpoint measure-preservation fact (BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianEndpoint) establishes this for $\rho\in[-1,1]$. Now hold fixed the event that the first coordinate's Gaussian CDF is at most $\alpha$, and vary the CDF threshold for this Gaussian linear combination. The bound for changing a Gaussian CDF threshold inside a fixed event (BooleanAnalysis.GaussianSpace.abs_measureReal_standardGaussianCDF_inter_sub_le) gives the desired estimate. Reordering the intersection identifies these two events with the defining events for the two stabilities.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianEndpoint`, `BooleanAnalysis.GaussianSpace.abs_measureReal_standardGaussianCDF_inter_sub_le`.
