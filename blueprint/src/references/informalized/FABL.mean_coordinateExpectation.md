<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_coordinateExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Preserved by Coordinate Averaging

**Claim.** Replacing each value of a real-valued function by the average of its values with a chosen coordinate set to each sign leaves its mean unchanged.

**Proof.** The coordinate Laplacian of $f$ is the difference between $f$ and its coordinate average. Its mean is zero: the mean equals the Fourier coefficient at the empty set (FABL.mean_eq_fourierCoeff_empty), and the Fourier coefficient of the coordinate Laplacian is zero at that set because the empty set does not contain the chosen coordinate (FABL.fourierCoeff_coordinateLaplacian). Thus the mean of $f$ minus the mean of its coordinate average is zero, using linearity of expectation. Rearranging gives the result.

**Key facts.** `FABL.mean_eq_fourierCoeff_empty`, `FABL.fourierCoeff_coordinateLaplacian`.
