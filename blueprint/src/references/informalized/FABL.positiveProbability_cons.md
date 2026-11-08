<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.positiveProbability_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Decomposition of Positive Probability

**Claim.** The uniform probability that $f$ equals $1$ is the average of the corresponding probabilities for the restrictions obtained by fixing the first coordinate to $1$ and to $-1$.

**Proof.** Unfold positive probability as the uniform expectation of the indicator of the event $f(x)=1$. The expectation on the $(n+1)$-dimensional cube splits into the average of the expectations on the two slices with first coordinate fixed, by the coordinate decomposition formula (`expect_fin_cons`). On each slice, the indicator is exactly the indicator that the corresponding first-coordinate restriction equals $1$, so those expectations are the two stated positive probabilities.

**Key facts.** `FABL.expect_fin_cons`.
