<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_c1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the First-Search Count

**Claim.** Replacing the seventeenth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose first-search count $c_1$ is $k$.

**Proof.** At an arbitrary coordinate, the two functions agree: the first-search count $c_1$ occupies the seventeenth position, where both updates yield $k$, and every other position retains its original field. Thus the register vectors are equal.
