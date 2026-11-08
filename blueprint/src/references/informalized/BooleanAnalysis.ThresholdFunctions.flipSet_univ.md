<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.flipSet_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping Every Coordinate

**Claim.** Flipping every coordinate of a Boolean vector produces the vector obtained by complementing each coordinate.

**Proof.** At any coordinate $i$, membership in the universal set is automatic. By the definition of the set flip, that coordinate is therefore replaced by its Boolean complement. Since this holds for every coordinate, the flipped vector is the function $i\mapsto !x_i$.
