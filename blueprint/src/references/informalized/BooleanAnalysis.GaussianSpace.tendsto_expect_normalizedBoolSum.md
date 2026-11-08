<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.tendsto_expect_normalizedBoolSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian limit for Lipschitz functions of cube sums

**Claim.** For every Lipschitz function, its expectation on the normalized sum of independent uniform Boolean signs converges to its expectation under the standard Gaussian measure.

**Proof.** The integral of a function on the finite Boolean cube under the product of uniform Boolean measures equals its uniform cube average (`integral_uniformBool_pi_eq_expect`). Apply this identity to the function obtained by evaluating $\psi$ on the normalized sign sum. The resulting sequence of integrals converges to the standard Gaussian integral by the central limit result for Lipschitz functions (`tendsto_integral_normalizedBoolSum`), which proves the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_uniformBool_pi_eq_expect`, `BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolSum`.
