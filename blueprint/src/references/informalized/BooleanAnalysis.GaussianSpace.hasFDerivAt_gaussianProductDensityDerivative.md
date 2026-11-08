<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensityDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the product density derivative

**Claim.** For a finite index set $I$, variance $v\geq0$, and $c,z\in\mathbb R^I$, the derivative, as a function of its mean vector, of the product Gaussian density derivative at $c$ sends directions $h,k$ to $G_v(c,z)\bigl(S_v(c,z)[h]S_v(c,z)[k]-\sum_i h_i k_i/v\bigr)$.

**Proof.** First express the derivative of the product density as the product density times its score linear functional (\texttt{gaussianProductDensityDerivative\_eq\_density\_smul\_score}). The product density is differentiable in its mean vector with derivative given by the product density derivative (\texttt{hasFDerivAt\_gaussianProductDensity}), and the score is differentiable with derivative sending $h$ to the functional $k\mapsto-\sum_i h_i k_i/v$ (\texttt{hasFDerivAt\_gaussianProductDensityScore}). Applying the product rule to density times score gives the derivative of the density multiplied by the score, plus the density multiplied by the score's derivative. Evaluated on directions $h,k$, these terms combine to $G_v(c,z)S_v(c,z)[h]S_v(c,z)[k]$ and $-G_v(c,z)\sum_i h_i k_i/v$, respectively.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityDerivative_eq_density_smul_score`, `BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensity`, `BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensityScore`.
