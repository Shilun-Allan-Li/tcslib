<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Scratch Register

**Claim.** Replacing the thirteenth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose scratch register $Z$ is $k$.

**Proof.** Compare the vectors at an arbitrary coordinate. The scratch register $Z$ occurs in the thirteenth position of the ordered list of state fields. There, updating the vector and setting $Z$ to $k$ both give $k$; at every other position, both sides retain the original field. Hence the vectors agree at all coordinates.
