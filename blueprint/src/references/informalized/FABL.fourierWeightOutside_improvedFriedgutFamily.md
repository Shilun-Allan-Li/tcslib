<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.fourierWeightOutside_improvedFriedgutFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exterior Weight and the Improved Friedgut Family

**Claim.** The Fourier weight outside the improved Friedgut family equals the sum over sets of size at most $k$ that are not contained in the coordinates whose Boolean influence reaches the improved Friedgut threshold.

**Proof.** A set lies outside the improved Friedgut family precisely when it is not contained in the threshold-influential coordinates and does not have size greater than $k$. The latter condition is equivalent to having size at most $k$. Hence the two sums have the same indexing sets and the same squared Fourier-coefficient summands, so they are equal.
