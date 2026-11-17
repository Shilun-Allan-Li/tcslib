<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch-Register Coordinate

**Claim.** For every state $S$, the scratch-register coordinate of its 17-entry register vector is $S.Z$.

**Proof.** The vector lists the state fields in order, with $S.Z$ in position $12$. The scratch-register coordinate has that index, so evaluating the vector there returns $S.Z$ by its definition.
