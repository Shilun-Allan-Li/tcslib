<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.flipSet_flipSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of a Coordinate Flip

**Claim.** Flipping the coordinates in a set $S$ twice returns the original vector.

**Proof.** Compare the two vectors at each coordinate. If the coordinate belongs to $S$, it is complemented twice, returning its original Boolean value. If it does not belong to $S$, neither flip changes it. The vectors therefore agree at every coordinate.
