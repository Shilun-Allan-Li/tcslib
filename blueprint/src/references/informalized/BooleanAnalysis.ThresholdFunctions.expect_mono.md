<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Uniform Expectation

**Claim.** If two real-valued functions on the Boolean cube satisfy $f(x)\le g(x)$ at every point, then the uniform expectation of $f$ is at most the uniform expectation of $g$.

**Proof.** Express both uniform expectations as expectations over the finite cube (BooleanAnalysis.expect_eq_fintypeExpect). The finite-expectation monotonicity principle says that pointwise order implies order of expectations, so the assumed inequality at each cube point yields the result.

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
