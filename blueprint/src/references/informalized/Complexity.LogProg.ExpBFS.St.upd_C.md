<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_C -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift Counter Update

**Claim.** Replacing coordinate $13$ of the register vector by $k$ gives the register vector of the state with shift counter $k$.

**Proof.** To prove equality of the two register vectors, compare their values at an arbitrary coordinate. At coordinate $13$, the update replaces the old entry by $k$, and the state update makes that same entry the new shift counter $k$. At every other coordinate, both constructions retain the original register. Thus the vectors agree at every coordinate, so they are equal.
