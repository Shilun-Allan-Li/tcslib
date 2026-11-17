<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.gstep_tmove -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of abstract and tape-head moves

**Claim.** For a valid tape-head position consistent with the flags, the abstract update and the tape-head move select the same segment, preserve consistency, and either describe a within-segment coordinate change or a boundary crossing with zero abstract movement.

**Proof.** Fix the segment and position, and identify the chosen segment with its word and doubling flag. Validity supplies the index bound whenever the position is a cell. Split on the movement and on whether the position is a left boundary, cell, or right boundary; in each case the definitions of the abstract update and tape-head move give the result directly.

For a zero move both constructions leave the position unchanged. For a positive move from a cell in a doubled segment, the parity condition determines whether the move changes only the parity flag; otherwise both descriptions advance to the next cell or to the right boundary. From a left boundary, the empty and nonempty word cases give, respectively, the right boundary or the first cell. From a right boundary, either the last-segment condition keeps the head at that boundary, or the move crosses to the next segment's left boundary. The consistency hypothesis handles the direction flags at boundaries and the parity flag in doubled cells. For negative moves, the same case analysis reverses these steps: in a doubled segment the parity condition may account for the move within the same cell; otherwise the move goes to the preceding cell or left boundary. From the left boundary, either the first-segment condition keeps the head there or the move crosses to the previous segment's right boundary. In every within-segment case the coordinate changes by the abstract movement output; at a crossing the output is zero. The segment-index tests agree because $s$ is in range, so the boundary cases are exactly the first and last segment cases specified in the abstract rule.
