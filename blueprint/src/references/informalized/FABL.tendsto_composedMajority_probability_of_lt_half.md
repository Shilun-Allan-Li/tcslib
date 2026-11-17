<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.tendsto_composedMajority_probability_of_lt_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed majority limit below half

**Claim.** For $0<p<1/2$, the biased minus-probability polynomial of the composed majority tends to $p^2$.

**Proof.** The composition probability formula expresses each term as $p^2+2p(1-p)$ times the odd-block majority probability (`composedMajority_probability_formula`). For $p<1/2$, that odd-block probability tends to zero (`tendsto_biasedMinusProbabilityPolynomial_majority_odd_of_lt_half`). The constant term therefore remains, and the limit is $p^2$.

**Key facts.** `FABL.tendsto_biasedMinusProbabilityPolynomial_majority_odd_of_lt_half`, `FABL.composedMajority_probability_formula`.
