<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outward-Walk Counter Coordinate

**Claim.** For every state $S$, the outward-walk-counter coordinate of its 17-entry register vector is $S.T$.

**Proof.** The vector lists the state fields in order, with $S.T$ in position $10$. The outward-walk-counter coordinate has that index, so evaluating the vector there returns $S.T$ by its definition.
