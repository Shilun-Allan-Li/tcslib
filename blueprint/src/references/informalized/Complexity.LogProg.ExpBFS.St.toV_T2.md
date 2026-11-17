<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_T2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return-Walk Counter Coordinate

**Claim.** For every state $S$, the return-walk-counter coordinate of its 17-entry register vector is $S.T2$.

**Proof.** The vector lists the state fields in order, with $S.T2$ in position $11$. The return-walk-counter coordinate has that index, so evaluating the vector there returns $S.T2$ by its definition.
