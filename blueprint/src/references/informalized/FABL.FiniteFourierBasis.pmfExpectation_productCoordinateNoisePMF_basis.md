<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.pmfExpectation_productCoordinateNoisePMF_basis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Coordinate Noise on a Basis Vector

**Claim.** The expectation of a basis vector under the one-coordinate noise distribution at $x$ is $1$ for the constant basis index and otherwise is $\rho$ times its value at $x$.

**Proof.** The one-coordinate noise expectation is $\rho$ times the value at $x$, plus $(1-\rho)$ times the expectation under the original distribution (\(\texttt{FABL.pmfExpectation_productCoordinateNoisePMF}\)). The basis vector's original expectation is $1$ at the distinguished constant index and $0$ at every other index (\(\texttt{FABL.FiniteFourierBasis.expect_basis}\)). If the index is distinguished, the basis vector is identically one, so the noise expectation is also one. Otherwise its original expectation vanishes, leaving $\rho$ times its value at $x$.

**Key facts.** `FABL.pmfExpectation_productCoordinateNoisePMF`, `FABL.FiniteFourierBasis.expect_basis`.
