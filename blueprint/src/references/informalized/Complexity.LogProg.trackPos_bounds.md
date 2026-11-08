<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.trackPos_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on Track Positions

**Claim.** For any valid track position, its associated integer position lies between $-1$ and the length of the segment, inclusive.

**Proof.** Split into the three possible forms of a track position. At the left boundary the position is $-1$, so both bounds hold. At the right boundary it is the segment length, so again both bounds hold. For a cell position with index $c$, validity says $c$ is smaller than the segment length; since both are natural numbers, this gives $-1\le c$ and $c\le L$.
