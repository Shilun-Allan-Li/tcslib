<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_s1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Next Radius

**Claim.** Replacing the fourth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose next radius $s_1$ is $k$.

**Proof.** Compare the vectors coordinate by coordinate. The next radius $s_1$ is the fourth listed field, where both updates give $k$. At every other coordinate, both sides keep the original field. This proves equality of the register vectors.
