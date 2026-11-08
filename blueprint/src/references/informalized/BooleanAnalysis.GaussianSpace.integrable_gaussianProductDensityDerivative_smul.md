<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianProductDensityDerivative_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the weighted Gaussian density derivative

**Claim.** For finite $I$, measurable $f$ bounded in absolute value by $1$, positive variance $v$, and any mean vector $c$, the function obtained by multiplying $f$ by the Gaussian product density derivative is integrable as a continuous-linear-functional-valued function under Lebesgue measure.

**Proof.** Choose an integrable nonnegative function $b$ that uniformly dominates the norm of the Gaussian product density derivative whenever the mean coordinates stay within a fixed bound (`gaussianProductDensity_derivative_dominated`). Taking that bound to be $\|c\|$ applies to the given mean vector, since each coordinate satisfies $|c_i|\le\|c\|$. Multiplication by $f$ increases the norm by the factor $|f(z)|\le1$, so the resulting function is still dominated by $b$. Its strong measurability follows from measurability of $f$ and continuity of the density-derivative map (`continuous_gaussianProductDensityDerivative`). The integrable domination criterion now gives integrability.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensity_derivative_dominated`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative`.
