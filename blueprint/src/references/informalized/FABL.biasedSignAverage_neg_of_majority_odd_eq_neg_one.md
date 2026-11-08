<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedSignAverage_neg_of_majority_odd_eq_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Average from Negative Majority

**Claim.** For every natural number $m$ and every sign vector $x$ of length $2m+1$, if the majority of its coordinates is $-1$, then the average of its coordinates is strictly negative.

**Proof.** Let $S=\sum_i \operatorname{signValue}(x_i)$. If $S$ were nonnegative, the threshold defining the majority would assign the value $1$. This contradicts the assumed majority value $-1$, since the two signs are distinct. Thus $S<0$. The denominator $2m+1$ is positive, so dividing $S$ by it preserves strict negativity.
