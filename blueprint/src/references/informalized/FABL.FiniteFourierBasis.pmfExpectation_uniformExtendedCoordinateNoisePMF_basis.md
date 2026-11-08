<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.FiniteFourierBasis.pmfExpectation_uniformExtendedCoordinateNoisePMF_basis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Extended Noise on a Basis Vector

**Claim.** For the uniform measure and the stated admissible range of $\rho$, the expectation of a basis vector under the extended one-coordinate noise at $x$ is $1$ at the distinguished constant index and otherwise is $\rho$ times its value at $x$.

**Proof.** The expectation under the extended noise is $\rho$ times the value at $x$, plus $(1-\rho)$ times the uniform expectation (\(\texttt{FABL.pmfExpectation_uniformExtendedCoordinateNoisePMF}\)). The uniform expectation of a basis vector agrees with its expectation under the uniform probability mass function (\(\texttt{FABL.pmfExpectation_uniformPMF_eq_expect}\)); orthonormality and the constant-vector condition make this expectation $1$ at the distinguished index and $0$ otherwise (\(\texttt{FABL.FiniteFourierBasis.expect_basis}\)). At the distinguished index the vector is identically one, so the result is $1$. At every other index the uniform term vanishes, leaving $\rho$ times the value at $x$.

**Key facts.** `FABL.pmfExpectation_uniformExtendedCoordinateNoisePMF`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.FiniteFourierBasis.expect_basis`.
