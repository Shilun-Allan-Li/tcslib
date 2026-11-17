<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target-Code Coordinate

**Claim.** For every state $S$, the target-code coordinate of its 17-entry register vector is $S.V$.

**Proof.** The vector lists the state fields in order, with $S.V$ in position $9$. The target-code coordinate has that index, so evaluating the vector there returns $S.V$ by its definition.
