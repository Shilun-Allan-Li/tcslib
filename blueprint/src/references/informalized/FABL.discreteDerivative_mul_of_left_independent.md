<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.discreteDerivative_mul_of_left_independent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Product with an Independent Factor

**Claim.** If changing coordinate $i$ leaves $q$ unchanged, then the discrete derivative of $qr$ at $x$ is $q(x)$ times the discrete derivative of $r$ at $x$.

**Proof.** By the pointwise formula for the discrete derivative ($\texttt{FABL.discreteDerivative\_apply}$), the left side is the difference of the values of $qr$ at the two points obtained by setting coordinate $i$ to $1$ and $-1$, divided by $2$. Coordinate independence makes the corresponding values of $q$ equal to $q(x)$. Factoring this common value out of the difference gives $q(x)$ times the discrete derivative of $r$ at $x$.

**Key facts.** `FABL.discreteDerivative_apply`.
