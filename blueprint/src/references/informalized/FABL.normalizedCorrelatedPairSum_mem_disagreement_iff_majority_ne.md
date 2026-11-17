<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.normalizedCorrelatedPairSum_mem_disagreement_iff_majority_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Disagreement Criterion

**Claim.** For odd $n$, the normalized pair sum lies in the disagreement region exactly when the two sign vectors have different majorities.

**Proof.** Let $s_x$ and $s_y$ be the sums of the signs in the two vectors, and let $c=(\sqrt n)^{-1}$. Since $n$ is odd, neither sign sum is zero (\texttt{FABL.sum_signValue_ne_zero_of_odd}); also $c>0$. The two coordinates of the normalized pair sum are $cs_x$ and $cs_y$ (\texttt{FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum} and \texttt{FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum}). The threshold signs of $s_x,s_y$ differ exactly when $s_xs_y<0$ (\texttt{FABL.thresholdSign_ne_iff_mul_neg}). Because $c^2>0$, the product $(cs_x)(cs_y)=c^2s_xs_y$ is negative exactly when $s_xs_y$ is negative. This is precisely membership in the disagreement region, proving both directions.

**Key facts.** `FABL.sum_signValue_ne_zero_of_odd`, `FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum`, `FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum`, `FABL.thresholdSign_ne_iff_mul_neg`.
