<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productCovariance_const_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Covariance with a constant function

**Claim.** The covariance, under the product distribution, of the constant function with value $c$ and $g$ is zero.

**Proof.** The mean of the constant function is $c$ (`pmfExpectation_const`). Therefore its centered value is identically zero. The integrand defining covariance is consequently zero at every point, and the expectation of the zero function is zero, again by the constant-expectation identity.

**Key facts.** `FABL.pmfExpectation_const`.
