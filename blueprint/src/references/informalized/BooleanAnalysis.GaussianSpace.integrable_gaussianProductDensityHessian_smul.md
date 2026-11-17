<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianProductDensityHessian_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the weighted Gaussian density Hessian

**Claim.** For finite $I$, measurable $f$ bounded in absolute value by $1$, positive variance $v$, and mean vector $c$, multiplying the Gaussian product density Hessian by $f$ gives an integrable bilinear-form-valued function under Lebesgue measure.

**Proof.** An integrable nonnegative function $b$ uniformly dominates the norm of the Gaussian product density Hessian for all mean vectors whose coordinates are bounded by a prescribed constant (`gaussianProductDensityHessian_dominated`). Choose that constant as $\|c\|$; each coordinate of $c$ is bounded by this norm. Since $|f(z)|\le1$, the norm of the weighted Hessian at each $z$ remains at most $b(z)$. The Hessian is measurable because it is the restriction of the jointly continuous Hessian map to the fixed mean vector, and multiplication by measurable $f$ preserves measurability (`continuous_gaussianProductDensityHessian_joint`). The integrable domination criterion proves the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_dominated`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityHessian_joint`.
