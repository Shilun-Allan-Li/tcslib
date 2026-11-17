<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.hammingUpperTailIndicator_isSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the upper-tail indicator

**Claim.** For every dimension and threshold, the indicator of the event that the normalized Rademacher sum exceeds the threshold is invariant under every permutation of coordinates.

**Proof.** Fix a coordinate permutation and a point of the sign cube. The normalized Rademacher sum has the same value at the permuted point as at the original point, by permutation invariance of the sum (\(\texttt{FABL.normalizedRademacherSum_permuteInput}\)). Consequently, the two comparisons with the threshold have the same truth value, so the indicator takes the same value at both points.

**Key facts.** `FABL.normalizedRademacherSum_permuteInput`.
