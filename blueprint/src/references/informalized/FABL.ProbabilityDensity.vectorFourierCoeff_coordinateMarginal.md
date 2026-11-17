<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.ProbabilityDensity.vectorFourierCoeff_coordinateMarginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of coordinate marginals

**Claim.** The Fourier coefficient of the coordinate marginal of $\phi$ on $J$, at frequency $\gamma$, equals the Fourier coefficient of $\phi$ at the lifted frequency corresponding to $\gamma$.

**Proof.** Express each vector Fourier coefficient as the expectation of the density times its Walsh character (\(\texttt{FABL.vectorFourierCoeff_eq_expect}\)). The coordinate marginal is a pushforward under the projection onto $J$, and expectation under a pushforward equals the original expectation after composing the test function with that projection (\(\texttt{FABL.ProbabilityDensity.pushforward_expectation}\)). The Walsh character at $\gamma$, evaluated on the projected point, is exactly the Walsh character at the lifted frequency evaluated on the original point (\(\texttt{FABL.vectorWalshCharacter_coordinateProjection}\)). Thus the two expectation expressions agree pointwise inside the expectation, proving the equality.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.ProbabilityDensity.pushforward_expectation`, `FABL.vectorWalshCharacter_coordinateProjection`.
