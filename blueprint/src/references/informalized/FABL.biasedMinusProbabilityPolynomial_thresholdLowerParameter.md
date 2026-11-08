<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedMinusProbabilityPolynomial_thresholdLowerParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Probability Level

**Claim.** For a monotone, nonconstant Boolean function on the $n$-dimensional sign cube and $0<\epsilon<1/2$, the biased-minus probability polynomial at the lower parameter corresponding to level $\epsilon$ equals $\epsilon$.

**Proof.** By definition, the lower parameter is the biased probability level for the value $\epsilon$. The level identity for the biased probability level (\texttt{FABL.biasedMinusProbabilityPolynomial_biasedProbabilityLevel}) states that the polynomial evaluated at this parameter equals the specified level. The hypotheses ensure that $\epsilon$ lies in $(0,1)$, so this identity applies and gives the result.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_biasedProbabilityLevel`.
