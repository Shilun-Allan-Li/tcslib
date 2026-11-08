<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.discreteDerivative_mul_of_right_independent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Product with an Independent Factor

**Claim.** If changing coordinate $i$ leaves $r$ unchanged, then the discrete derivative of $qr$ at $x$ is the discrete derivative of $q$ at $x$ times $r(x)$.

**Proof.** Expand the derivative of the product using its pointwise formula ($\texttt{FABL.discreteDerivative\_apply}$). At both points used in the difference, coordinate independence identifies the value of $r$ with $r(x)$. Factoring this common value from the difference leaves $r(x)$ times the discrete derivative of $q$ at $x$; commutativity of real multiplication gives the stated order of factors.

**Key facts.** `FABL.discreteDerivative_apply`.
