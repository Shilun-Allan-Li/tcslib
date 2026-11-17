<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Width Factor

**Claim.** Replacing the fifth coordinate of a state’s 17-component register vector by $k$ gives the register vector of the state whose width factor $X$ is $k$.

**Proof.** To compare the two register vectors, evaluate them at an arbitrary coordinate. The vectors list the state fields in order, with $X$ in the fifth position. At that position, updating the coordinate replaces $X$ by $k$, exactly as does updating the state field. At every other position, neither update changes the listed field. Thus the two functions agree at every coordinate and are equal.
