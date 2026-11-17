<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussian_polynomial_dense -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density of Gaussian polynomials

**Claim.** For every finite $p\ge 1$, every function in Gaussian $L^p$ can be approximated arbitrarily closely in $L^p$ by a real multivariate polynomial.

**Proof.** View the real-valued function as complex-valued. The range of the Gaussian polynomial map is dense in complex Gaussian $L^p$, by the dense-range criterion and the fact that the closure of that range is the whole space (`gaussianPolynomialLp_closure_eq_top`). Thus, for any prescribed error, choose a complex polynomial whose Gaussian $L^p$ class is within that error of the given function. Replace this polynomial by a real polynomial whose evaluation is the real part of the complex polynomial's evaluation (`exists_real_polynomial_re`). At each point, the absolute value of the difference between the real function and this real polynomial is at most the complex modulus of the original difference, since the absolute value of a complex number's real part is bounded by its modulus. Monotonicity of the $L^p$ norm transfers the approximation bound to the real polynomial. Polynomial evaluations have the required $L^p$ membership (`memLp_eval_gaussian`).

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPolynomialLp_closure_eq_top`, `BooleanAnalysis.GaussianSpace.memLp_eval_gaussian`, `BooleanAnalysis.GaussianSpace.exists_real_polynomial_re`.
