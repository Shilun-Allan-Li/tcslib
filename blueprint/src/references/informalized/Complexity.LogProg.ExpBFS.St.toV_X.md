<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width-Factor Coordinate

**Claim.** For every state $S$, the width-factor coordinate of its 17-entry register vector is $S.X$.

**Proof.** The vector lists the state fields in order, with $S.X$ in position $4$. The width-factor coordinate has that index, so evaluating the vector there returns $S.X$ by its definition.
