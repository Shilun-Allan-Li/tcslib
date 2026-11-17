<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar multiplication of Hermite coefficients

**Claim.** For any dimension, real scalar $c$, function $f$, and multi-index $\alpha$, the Hermite coefficient of $cf$ at $\alpha$ equals $c$ times the Hermite coefficient of $f$ at $\alpha$.

**Proof.** By definition, the coefficient of $cf$ is the integral of $(c f(x))$ times the Hermite function. Associativity of multiplication rewrites the integrand as $c$ times the integrand defining the coefficient of $f$. Pulling the constant scalar outside the integral gives the result.
