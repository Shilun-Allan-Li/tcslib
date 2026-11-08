<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_conditional_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Integral Formula

**Claim.** When $-1<\rho<1$ and $\alpha,\beta\in(0,1)$, the Gaussian bivariate stability equals the integral of the conditional Gaussian distribution function up to the quantile for $\alpha$, as displayed in the statement.

**Proof.** First replace the two CDF threshold conditions in the definition of bivariate stability by the corresponding inequalities against the quantiles of $\alpha$ and $\beta$. This is the threshold representation of bivariate stability (\texttt{BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_threshold}). Apply the scalar joint-threshold integral formula (\texttt{BooleanAnalysis.GaussianSpace.scalarGaussian_joint_threshold_integral}) with thresholds $s=\Phi^{-1}(\alpha)$ and $t=\Phi^{-1}(\beta)$. Its required scale is positive: since $-1<\rho<1$, we have $1-\rho^2>0$, hence $\sqrt{1-\rho^2}>0$. Substitution gives precisely the stated integral.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_threshold`, `BooleanAnalysis.GaussianSpace.scalarGaussian_joint_threshold_integral`.
