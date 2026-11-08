<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_ch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Change Flag

**Claim.** Replacing the fifteenth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose change flag $ch$ is $k$.

**Proof.** Check the two functions at an arbitrary coordinate. The change flag $ch$ is listed fifteenth, and both updates give $k$ there. At all other coordinates, both sides retain the corresponding original field. Consequently the functions, and hence the register vectors, are equal.
