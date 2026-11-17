<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_u -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the source register

**Claim.** Replacing coordinate $13$ of the register vector by $v$ gives the vector of the state obtained by replacing its source register $u$ by $v$.

**Proof.** Both sides are functions on the fifteen coordinates. At coordinate $13$, the update replaces the entry $u$ by $v$, matching the updated state. At every other coordinate, the update leaves the entry unchanged, and the corresponding state register is unchanged. Thus the two vectors agree at every coordinate.
