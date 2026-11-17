<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/FourierConcentration.lean :: RestrictionFourier.sum_prob_inter_eq_card_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition by intersection size

**Claim.** For every real $p$, summing the probabilities of the events $U\cap J=S$ over all subsets $S$ of size at least $k$ gives the probability that $|U\cap J|\ge k$.

**Proof.** Fix a restriction $\rho$. In the sum over $S$, the indicator of $U\cap\rho.\mathrm{freeVars}=S$ is nonzero for exactly one subset, namely $S=U\cap\rho.\mathrm{freeVars}$. Thus the sum of the weighted indicators, retaining only subsets with $|S|\ge k$, equals the restriction weight times the indicator that $|U\cap\rho.\mathrm{freeVars}|\ge k$. Summing this pointwise identity over all restrictions proves the result: the finite sums can be interchanged, and the defining sums for the two probabilities are exactly the resulting expressions.
