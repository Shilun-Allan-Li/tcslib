<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.expect_coordinateSign_mul_eq_expect_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Sign and Discrete Derivative

**Claim.** For a function on the sign cube, the uniform average of its product with the sign in coordinate $i$ equals the uniform average of its discrete derivative in coordinate $i$.

**Proof.** For each cube point $x$, the decomposition identity (\texttt{eq\_signValue\_mul\_discreteDerivative\_add\_coordinateExpectation}) expresses $q(x)$ as its coordinate sign times its discrete derivative, plus its coordinate expectation. Since the coordinate sign is $1$ or $-1$, this rearranges to the pointwise identity that the sign times $q(x)$ is the discrete derivative plus the sign times the coordinate expectation. The latter summand has average zero: flipping coordinate $i$ leaves the coordinate expectation unchanged, by invariance under setting that coordinate to either sign (\texttt{coordinateExpectation\_setCoordinate}), while it negates the coordinate sign. The average of a function that changes sign under this measure-preserving flip vanishes (\texttt{expect\_eq\_zero\_of\_flipCoordinate\_neg}). Averaging the pointwise identity and using additivity of expectation therefore gives the result.

**Key facts.** `FABL.eq_signValue_mul_discreteDerivative_add_coordinateExpectation`, `FABL.coordinateExpectation_setCoordinate`, `FABL.expect_eq_zero_of_flipCoordinate_neg`.
