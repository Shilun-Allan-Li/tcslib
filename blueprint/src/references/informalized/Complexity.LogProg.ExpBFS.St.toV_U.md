<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source-Code Coordinate

**Claim.** For every state $S$, the source-code coordinate of its 17-entry register vector is $S.U$.

**Proof.** The vector lists the state fields in order, with $S.U$ in position $8$. The source-code coordinate has that index, so evaluating the vector there returns $S.U$ by its definition.
