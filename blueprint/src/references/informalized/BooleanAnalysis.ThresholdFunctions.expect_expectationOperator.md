<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.expect_expectationOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Averaging Preserves Expectation

**Claim.** For a coordinate of the Boolean cube, averaging a function over the two possible values of that coordinate preserves its uniform expectation.

**Proof.** Fix a cube point $x$. Setting coordinate $i$ to either Boolean value gives either $x$ itself or the point obtained by flipping coordinate $i$. Thus the coordinate average at $x$ equals $\bigl(g(x)+g(x^{\{i\}})\bigr)/2$. The flip map is an involution, since flipping the same coordinate twice returns the original point (BooleanAnalysis.flipBit_flipBit); consequently it permutes the finite cube, so summing $g$ over flipped points gives the same total as summing $g$ over the cube. Summing the displayed average therefore gives the original sum of $g$, after which the common uniform weight and the factor of two cancel.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.update_eq_ite_flipBit`, `BooleanAnalysis.flipBit_flipBit`.
