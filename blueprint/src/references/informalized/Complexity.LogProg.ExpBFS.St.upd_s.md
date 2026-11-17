<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Radius

**Claim.** Replacing the third coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose radius $s$ is $k$.

**Proof.** The radius $s$ is the third field in the register vector. At that coordinate, both the vector update and the state update give $k$; at every other coordinate, each gives the original field. The two register vectors therefore agree at every coordinate.
