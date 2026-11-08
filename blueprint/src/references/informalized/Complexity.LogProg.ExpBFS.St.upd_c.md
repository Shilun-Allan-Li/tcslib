<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Marked-Code Count

**Claim.** Replacing the sixteenth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose marked-code count $c$ is $k$.

**Proof.** Evaluate both vectors at an arbitrary coordinate. The marked-code count $c$ is the sixteenth listed field, so at that coordinate both updates give $k$. At every other coordinate, both vectors give the original listed field. Therefore the functions agree everywhere.
