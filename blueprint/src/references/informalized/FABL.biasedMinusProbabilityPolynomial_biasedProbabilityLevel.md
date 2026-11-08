<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedMinusProbabilityPolynomial_biasedProbabilityLevel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the Biased Probability Level

**Claim.** At the uniquely specified parameter in $(0,1)$ where the biased minus-probability polynomial equals $\alpha$, the polynomial indeed has value $\alpha$.

**Proof.** The existence-and-uniqueness result (`existsUnique_biasedMinusProbabilityPolynomial_eq`) supplies a parameter and the conjunction that it lies in $(0,1)$ and has polynomial value $\alpha$. The biased probability level is defined to be the parameter selected from that result. Its defining selection therefore satisfies the value equality.

**Key facts.** `FABL.existsUnique_biasedMinusProbabilityPolynomial_eq`.
