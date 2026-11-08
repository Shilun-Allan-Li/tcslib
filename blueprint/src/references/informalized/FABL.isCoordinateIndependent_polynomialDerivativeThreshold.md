<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.isCoordinateIndependent_polynomialDerivativeThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Independence of a Derivative Threshold

**Claim.** For any real-valued function on the sign cube and coordinate $i$, thresholding its discrete derivative in direction $i$ gives a sign-valued function whose real-valued version is unchanged when coordinate $i$ of the input is replaced by either sign.

**Proof.** Fix an input $x$ and a sign $b$. By the discrete-derivative identity `discreteDerivative_setCoordinate`, the derivative in direction $i$ at the input obtained by replacing coordinate $i$ of $x$ with $b$ equals the derivative at $x$. Applying the same threshold function to equal real numbers gives equal signs; passing to their real values preserves that equality. This is exactly coordinate independence.

**Key facts.** `FABL.discreteDerivative_setCoordinate`.
