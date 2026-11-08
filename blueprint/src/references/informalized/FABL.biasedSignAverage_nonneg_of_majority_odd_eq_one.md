<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedSignAverage_nonneg_of_majority_odd_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Average from Positive Majority

**Claim.** For every natural number $m$ and every sign vector $x$ of length $2m+1$, if the majority of its coordinates is $1$, then the average of its coordinates is nonnegative.

**Proof.** Let $S=\sum_i \operatorname{signValue}(x_i)$. If $S<0$, the threshold defining the majority would assign the value $-1$, contradicting the assumed value $1$. Hence $S\ge 0$. Since $2m+1>0$, dividing by this denominator preserves nonnegativity, proving the claim.
