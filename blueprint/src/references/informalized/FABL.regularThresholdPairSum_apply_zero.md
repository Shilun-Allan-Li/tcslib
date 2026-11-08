<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPairSum_apply_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Coordinate of the Pair Sum

**Claim.** For each pair of sign vectors, the first coordinate of the sum of the vectors $(a_i x_i,a_i y_i)$ is $4\sum_{i<n}a_i x_i$.

**Proof.** Expand the pair sum and evaluate its first coordinate term by term. Each summand is represented by the two coordinates $a_i\,\mathrm{signValue}(x_i)$ and $a_i\,\mathrm{signValue}(y_i)$, so its first coordinate is $a_i\,\mathrm{signValue}(x_i)$. Summing these values gives exactly the defining sum for the linear form at $x$.
