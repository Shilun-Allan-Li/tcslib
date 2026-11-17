<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_y -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the query-length register

**Claim.** Replacing coordinate $0$ of the register vector by $v$ gives the vector of the state obtained by replacing its query-length register $y$ by $v$.

**Proof.** At coordinate $0$, the vector update replaces the entry $y$ by $v$, just as the state update does. At every other coordinate both constructions retain the original register value. Therefore the two vectors agree coordinatewise.
