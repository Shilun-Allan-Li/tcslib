<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductBounds.lean :: BooleanAnalysis.GaussianSpace.gaussianCoordinate_first_kernel_integrable_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Coordinate Gaussian Score Bound

**Claim.** For a finite product Gaussian measure with coordinate means $c_j$ and variance parameter $v>0$, any measurable $f$ bounded in absolute value by $1$ has an integrable first-coordinate score $(z_i-c_i)f(z)/v$, whose integral has absolute value at most $1+1/v$.

**Proof.** Since $v>0$, the pointwise estimate $|f(z)|\le 1$ and the elementary inequality $|z_i-c_i|\le (z_i-c_i)^2+1$ give
\[
\left|\frac{z_i-c_i}{v}f(z)\right|\le \frac{(z_i-c_i)^2+1}{v}.
\]
The right-hand side is integrable: the centered coordinate square is integrable (`integrable_centered_sq_gaussianCoordinate`), as is the constant function. This domination proves integrability of the score. The absolute value of its integral is at most the integral of its absolute value, which is in turn at most the integral of the displayed bound. The centered-square moment is $v$ (`integral_centered_sq_gaussianCoordinate`), while the constant integrates to $1$ under the product probability measure. Thus the bound is $(v+1)/v=1+1/v$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_centered_sq_gaussianCoordinate`, `BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianCoordinate`.
