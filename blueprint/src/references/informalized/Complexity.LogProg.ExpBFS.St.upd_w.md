<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_w -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Code Width

**Claim.** Replacing the sixth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose code width $w$ is $k$.

**Proof.** The code width $w$ occupies the sixth position in the register vector. At that position, updating the vector and updating the state field both give $k$; at all other positions, both leave the listed field unchanged. The vectors thus agree at every coordinate.
