<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.tendsto_composedMajority_probability_of_half_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed majority error above half

**Claim.** For $1/2<p<1$, the minus-probability of the composed majority tends to $1-(1-p)^2$ as $m$ tends to infinity.

**Proof.** For each $m$, the composed-majority probability equals $p^2+2p(1-p)$ times the odd-block majority probability, with the latter as the factor in the second term (`composedMajority_probability_formula`). The odd-block majority probability tends to $1$ when $p>1/2$ (`tendsto_biasedMinusProbabilityPolynomial_majority_odd_of_half_lt`). Taking the limit in this affine expression gives $p^2+2p(1-p)=1-(1-p)^2$.

**Key facts.** `FABL.tendsto_biasedMinusProbabilityPolynomial_majority_odd_of_half_lt`, `FABL.composedMajority_probability_formula`.
