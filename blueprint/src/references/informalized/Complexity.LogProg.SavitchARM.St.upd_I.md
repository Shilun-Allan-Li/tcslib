<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_I -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the level counter

**Claim.** Replacing coordinate $13$ of the register vector by $k$ gives the register vector of the state whose current level is $k$.

**Proof.** To prove equality of the two register vectors, compare their values at an arbitrary coordinate. The vector records the state fields in order, and the current-level field $I$ is at coordinate $13$. At that coordinate, both sides have value $k$; at every other coordinate, updating leaves the original entry unchanged, just as changing $I$ leaves all other state fields unchanged. Thus the vectors agree at every coordinate.
