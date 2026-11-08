<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.fourierCoeff_le_nonnegativeOddFourierMaximum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd coefficients bounded by their maximum

**Claim.** Every odd-cardinality Fourier coefficient of $f$ is at most the maximum of $0$ and the Fourier coefficients indexed by odd-cardinality subsets.

**Proof.** The given set $S$ belongs to the finite family of odd-cardinality frequencies by its assumed odd cardinality. Its Fourier coefficient therefore belongs to the image of that family under the coefficient map, and hence to the set obtained by adjoining $0$. Every member of a finite set is at most its maximum, giving the result.
