<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.measure_neg_centeredFourierObservation_sum_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower tail for centered Fourier observations

**Claim.** For a fixed target Boolean function and subset $S$, the probability that the negative sum of the centered Fourier observations over $m$ independent uniform samples is at least $m\varepsilon$ is at most $\exp(-((m\varepsilon)^2)/(2m))$.

**Proof.** Each sample-coordinate observation, centered by its expectation (the Fourier coefficient), is a sub-Gaussian random variable with parameter $1$ (`sampleCoordinate_fourierObservation_hasSubgaussianMGF`). Under the product measure, these centered observations are independent because they depend on separate coordinates. The independent-sum theorem preserves the sub-Gaussian bound for their sum. Applying its one-sided tail estimate to the negative of that sum, at the nonnegative threshold $m\varepsilon$, gives the asserted exponential bound.

**Key facts.** `FABL.sampleCoordinate_fourierObservation_hasSubgaussianMGF`.
