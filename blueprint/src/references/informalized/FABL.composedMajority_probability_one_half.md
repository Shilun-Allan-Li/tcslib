<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.composedMajority_probability_one_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unbiased Composed Majority

**Claim.** For every natural number $m$, the biased minus-probability polynomial of composed majority on $2+(2m+1)$ coordinates, evaluated at $p=1/2$, equals $1/2$.

**Proof.** Apply the composed-majority probability formula at $p=1/2$, which is allowed because $1/2$ lies strictly between $0$ and $1$. It expresses the desired value as $(1/2)^2+2(1/2)(1-1/2)$ times the biased minus-probability polynomial of majority on $2m+1$ coordinates at $1/2$. The latter polynomial equals $1/2$ by the unbiased-majority identity (`biasedMinusProbabilityPolynomial_majority_one_half`). Substitution gives $1/4+1/2\cdot1/2=1/2$.

**Key facts.** `FABL.composedMajority_probability_formula`, `FABL.biasedMinusProbabilityPolynomial_majority_one_half`.
