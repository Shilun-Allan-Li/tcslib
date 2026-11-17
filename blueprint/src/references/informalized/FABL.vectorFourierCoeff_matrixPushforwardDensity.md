<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.vectorFourierCoeff_matrixPushforwardDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a matrix pushforward

**Claim.** For a matrix $H$ over $\mathbb F_2$ and a probability density $\varphi$, the vector Fourier coefficient of the pushforward density at $\gamma$ equals the vector Fourier coefficient of $\varphi$ at $H\gamma$.

**Proof.** Write each vector Fourier coefficient as the expectation of the density against its Walsh character. By the pushforward expectation formula, the first expectation becomes the expectation under $\varphi$ of the Walsh character evaluated at $yH$. The Walsh character's compatibility with matrix multiplication identifies this value with the character indexed by $H\gamma$ evaluated at $y$. This is exactly the expectation defining the coefficient of $\varphi$ at $H\gamma$.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.ProbabilityDensity.pushforward_expectation`, `FABL.vectorWalshCharacter_vecMul`.
