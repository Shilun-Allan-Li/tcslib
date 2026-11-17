<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.fourierCoeff_leadingCoordinateTimes_tailFrequency_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing shifted Fourier coefficient

**Claim.** For the function formed by multiplying the first coordinate by $g$ and evaluating $g$ on the remaining coordinates, the Fourier coefficient at the shifted frequency corresponding to $S$ is zero.

**Proof.** The tail-frequency formula writes this coefficient as the average of the coefficients of the two slices at first coordinate $1$ and $-1$ (`FABL.fourierCoeff_tailFrequency`). These slices are respectively $g$ and $-g$. By linearity, their coefficients are $\widehat g(S)$ and $-\widehat g(S)$, whose average is zero.

**Key facts.** `FABL.fourierCoeff_tailFrequency`.
