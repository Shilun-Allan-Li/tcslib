<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.abs_gaussianBivariateStability_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bivariate Stability Continuity Bound

**Claim.** For a correlation parameter $\rho\in[-1,1]$ and thresholds $\alpha,\beta,\alpha',\beta'\in[0,1]$, changing both thresholds changes the Gaussian bivariate stability by at most $|\alpha-\alpha'|+|\beta-\beta'|$.

**Proof.** Insert the intermediate value $\operatorname{Stab}_\rho(\alpha',\beta)$. The triangle inequality bounds the absolute difference between the endpoint stabilities by the sum of the absolute differences from $\operatorname{Stab}_\rho(\alpha,\beta)$ to this intermediate value and from the intermediate value to $\operatorname{Stab}_\rho(\alpha',\beta')$. The first-coordinate Lipschitz bound, applied with second threshold $\beta$, bounds the first difference by $|\alpha-\alpha'|$. The second-coordinate Lipschitz bound, applied with first threshold $\alpha'$, bounds the second difference by $|\beta-\beta'|$. Adding these estimates proves the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_gaussianBivariateStability_sub_left_le`, `BooleanAnalysis.GaussianSpace.abs_gaussianBivariateStability_sub_right_le`.
