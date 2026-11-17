<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.uniformProbability_ne_zero_eq_firstCoordinateSlices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-coordinate slice formula

**Claim.** The uniform probability that a function on the $(n+1)$-dimensional sign cube is nonzero is the average of the corresponding probabilities for its two first-coordinate slices.

**Proof.** Apply the first-coordinate decomposition of expectation: the average of any function on the cube is the mean of its averages on the slices with first coordinate $1$ and $-1$ (the decomposition `expect_fin_cons`). Apply this to the indicator of the event that $f$ is nonzero. On each slice, that indicator is precisely the indicator that the corresponding first-coordinate slice of $f$ is nonzero. The resulting identity is the stated average.

**Key facts.** `FABL.expect_fin_cons`.
