<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.IsCoordinateIndependent.discreteDerivative_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Independence of the Derivative

**Claim.** If changing coordinate $j$ leaves $q$ unchanged and $i\ne j$, then changing coordinate $j$ also leaves the discrete derivative of $q$ in coordinate $i$ unchanged.

**Proof.** Fix an input $x$ and a sign $b$. The derivative at the input obtained by changing coordinate $j$ is the difference of the two values of $q$ obtained by setting coordinate $i$ first to $1$ and then to $-1$, divided by $2$. Since $i$ and $j$ are distinct, setting these two coordinates commutes: for either choice $c\in\{1,-1\}$, changing $j$ to $b$ and then $i$ to $c$ gives the same input as changing $i$ to $c$ and then $j$ to $b$. Coordinate independence of $q$ in coordinate $j$ therefore identifies each term in that difference with the corresponding value at the input where only coordinate $i$ was changed. The resulting difference is exactly the derivative at $x$, proving the claimed independence.

**Key facts.** `FABL.discreteDerivative_apply`.
