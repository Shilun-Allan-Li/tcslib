<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPairSum_apply_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Coordinate of the Threshold Pair Sum

**Claim.** The second coordinate of the sum of the vectors $(a_i x_i,a_i y_i)$ over all $i<n$ is $\sum_{i<n}a_i y_i$.

**Proof.** The second coordinate of each summand is $a_i$ times the sign value of the second sign vector at coordinate $i$. Taking the second coordinate commutes with the finite sum, so the result is the sum of these terms, which is exactly the linear form evaluated at the second vector.
