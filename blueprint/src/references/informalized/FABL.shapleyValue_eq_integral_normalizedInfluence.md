<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_eq_integral_normalizedInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral Formula Under Monotonicity and Boolean Range

**Claim.** For a monotone function on subsets taking only the values $0$ and $1$, the Shapley value at $i$ equals the integral from $0$ to $1$ of its Bernoulli marginal contribution.

**Proof.** The general integral formula for the Shapley value applies to every real-valued function on subsets, without requiring monotonicity or a Boolean range (`shapleyValue_eq_integral_bernoulliMarginalContribution`). Apply it to the given function and element $i$. The stated hypotheses are therefore compatible with the result but are not needed in this proof.

**Key facts.** `FABL.shapleyValue_eq_integral_bernoulliMarginalContribution`.
