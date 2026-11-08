<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.middleLayerIndicator_isSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Middle-Layer Indicator

**Claim.** For every $m$, the indicator of the middle layer in the sign cube of dimension $2m$ is invariant under every permutation of its coordinates.

**Proof.** Fix a coordinate permutation and a point $x$. The positive-coordinate count is unchanged when the coordinates are permuted (FABL.positiveCoordinateCount_permuteInput). The middle-layer indicator depends only on whether this count equals $m$, so that condition, and hence the indicator value, is unchanged by the permutation.

**Key facts.** `FABL.positiveCoordinateCount_permuteInput`.
