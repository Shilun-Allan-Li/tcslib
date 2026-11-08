<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.upd_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outward Walk Counter Update

**Claim.** Replacing coordinate $10$ of the register vector by $k$ gives the register vector of the state with outward walk counter $k$.

**Proof.** At an arbitrary coordinate, the two vectors agree: at coordinate $10$, each has value $k$, because the vector update and state update both change the outward walk counter; elsewhere, each preserves the original register. Therefore they are equal coordinatewise.
