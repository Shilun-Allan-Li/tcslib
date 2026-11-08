<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.fourierWeightOutside_improvedFriedgutSmallFamily_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Family Exterior Weight Bound

**Claim.** The Fourier weight outside the improved Friedgut small family is at most the sum of the weight outside the improved Friedgut family and the weight on sets of size greater than $k$.

**Proof.** For a set $S$, being outside the small family means that either $S$ is not contained in the threshold-influential coordinates, or $|S|>k$. In the first case, $S$ is outside the improved Friedgut family unless it has size greater than $k$; in the second case it is already included in the degree-greater-than-$k$ sum. Thus every summand on the left occurs at least once on the right. The right side may count a set in both sums, which only increases it because squared Fourier coefficients are nonnegative. Summing over all $S$ proves the inequality.
