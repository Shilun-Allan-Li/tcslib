<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedPairPMF_expect_signValue_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-coordinate mean

**Claim.** For every coordinate of the second sign vector in a correlated pair, the expected sign is zero.

**Proof.** Use the two-stage expectation rule to condition first on the initial vector $x$ (`pmfExpectation_bind`). For fixed $x$, the second coordinate's conditional expectation is computed by averaging the noise output. The coordinate sign function is the singleton monomial $\{i\}$; the noise-kernel monomial formula says its conditional expectation is $\rho x_i$ (`pmfExpectation_noiseKernel_monomial`). Averaging over uniform $x$ pulls the constant factor $\rho$ outside the expectation (`pmfExpectation_const_mul`). The uniform mean of $x_i$ is zero: identify it with the singleton monomial and use the uniform monomial expectation formula (`pmfExpectation_uniformPMF_eq_expect`, `expect_monomial`). Hence the second-coordinate mean is $\rho\cdot 0=0$.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_noiseKernel_monomial`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_monomial`.
