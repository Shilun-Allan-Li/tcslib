<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensityScore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the product Gaussian score

**Claim.** For a finite index set $I$, variance $v\geq0$, and $c,z\in\mathbb R^I$, the score $S_v(m,z)[h]=\sum_i((z_i-m_i)/v)h_i$ is differentiable at $c$. Its derivative sends $h$ to the linear functional $k\mapsto-\sum_i h_i k_i/v$.

**Proof.** The score is the finite sum over coordinates $i$ of the scalar coefficient $(z_i-m_i)/v$ multiplied by the coordinate projection functional. For each coordinate, the coefficient is affine in $m_i$, with derivative in direction $h$ equal to $-h_i/v$; composing with the coordinate projection and multiplying by that fixed functional gives the corresponding rank-one contribution. Summing these derivatives over all coordinates yields the functional $k\mapsto-\sum_i h_i k_i/v$, as claimed.
