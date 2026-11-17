<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.eLpNorm_two_eq_sqrt_hermiteCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficients Determine the Gaussian $L^2$ Norm

**Claim.** For $f\in L^2(\gamma_n)$, its $L^2$ norm equals the square root of the sum of squares of its normalized multivariate Hermite coefficients.

**Proof.** Represent $f$ by its element in the $L^2$ space. The inner product of that element with itself equals its norm squared, and the inner-product-to-integral identity expresses this as $\int f(x)^2\,d\gamma_n(x)$. The Hermite Plancherel identity ($hermite_plancherel$), applied with both functions equal to $f$, rewrites the same integral as $\sum_\alpha c_\alpha^2$. Thus the squared norm equals this sum. Taking the nonnegative square root gives the norm, and translating back from the $L^2$ norm to the stated extended-norm expression yields the claimed equality.

**Key facts.** `BooleanAnalysis.GaussianSpace.inner_toLp_eq_integral_mul`, `BooleanAnalysis.GaussianSpace.hermite_plancherel`.
