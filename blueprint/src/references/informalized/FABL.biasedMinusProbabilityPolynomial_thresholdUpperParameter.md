<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedMinusProbabilityPolynomial_thresholdUpperParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Probability Level

**Claim.** For a monotone, nonconstant Boolean function on the $n$-dimensional sign cube and $0<\epsilon<1/2$, the biased-minus probability polynomial at the upper parameter corresponding to level $1-\epsilon$ equals $1-\epsilon$.

**Proof.** The upper parameter is, by definition, the biased probability level for $1-\epsilon$. The bounds on $\epsilon$ imply $0<1-\epsilon<1$, so the level identity for the biased probability level (\texttt{FABL.biasedMinusProbabilityPolynomial_biasedProbabilityLevel}) applies. It says that the polynomial at this parameter equals the specified level, namely $1-\epsilon$.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_biasedProbabilityLevel`.
