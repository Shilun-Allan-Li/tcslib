<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.inPos_after -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input head position after a segment move

**Claim.** Under the stated validity and movement or boundary-crossing hypotheses, moving the input head by the specified amount when the segment is the first one, and otherwise not moving it, gives the input position encoding the new track position and segment.

**Proof.** First use the bound that the length of the first segment is at most the input length; this ensures the segment positions fit within the input-position range. Split according to the two alternatives in the hypothesis. In the first, the segment index stays fixed and the track coordinate changes by the movement. If this segment is the first one, the input position is the track coordinate shifted by one. The bounds on valid track positions place both coordinates between the left and right boundaries; checking the three possible movements (zero, one step right, or one step left) shows that the input-head movement gives exactly the shifted new coordinate, with the endpoint convention respected. If the segment is not first, its input position is the fixed right boundary of the first segment, so a zero move leaves it unchanged, as required. In the boundary-crossing alternative the movement is zero. Crossing from the right boundary of segment $s$ to the left boundary of segment $s+1$ gives the same input position on both sides, since each is the boundary between those segments. Crossing from the left boundary of segment $s$ to the right boundary of segment $s-1$ likewise preserves the encoded input position. These cases establish the stated equality.

**Key facts.** `Complexity.LogProg.wlen_zero_le`, `Complexity.LogProg.trackPos_bounds`, `Complexity.LogProg.moveInputPos_val`, `Turing.moveInputPos_zero`.
