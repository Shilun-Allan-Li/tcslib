<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.contDiff_one_integral_gaussianPDFReal_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Differentiability of a Gaussian average

**Claim.** For measurable $f$ bounded in absolute value by $1$ and any positive variance $v$, the Gaussian average $m\mapsto\int p_v(m,z)f(z)\,dz$ is continuously differentiable.

**Proof.** The derivative formula for the Gaussian average gives, at each mean $m$, the derivative $\int ((z-m)/v) p_v(m,z)f(z)\,dz$. In particular, the function is differentiable everywhere. The same formula expresses its derivative as a function of $m$, and the stated Lipschitz bound for this derivative implies that it is continuous. A function differentiable everywhere with continuous derivative is continuously differentiable, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_integral_gaussianPDFReal_mean`, `BooleanAnalysis.GaussianSpace.lipschitzWith_integral_gaussianPDFReal_meanDerivative`.
