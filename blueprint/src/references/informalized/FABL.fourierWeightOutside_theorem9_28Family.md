<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.fourierWeightOutside_theorem9_28Family -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exterior weight identity

**Claim.** The Fourier weight outside the threshold family equals the sum of squared Fourier coefficients over sets of size at most $k$ that are not contained in the coordinates whose Boolean influence reaches the stated threshold.

**Proof.** For any set $S$, being outside the threshold family means both that $S$ is not contained in the threshold-influential coordinates and that $|S|$ is not greater than $k$. The latter condition is exactly $|S|\le k$. Hence the indexing condition in the exterior sum is precisely the conjunction used to index the low-degree outside-influential mass. Both sums assign the same squared Fourier coefficient to every such $S$, so the sums are equal.
