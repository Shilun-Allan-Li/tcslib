<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the input-length register

**Claim.** Replacing coordinate $2$ of the register vector by $v$ gives the vector of the state obtained by replacing its input-length register $x$ by $v$.

**Proof.** Compare the two vectors coordinate by coordinate. At coordinate $2$, both have value $v$. At every other coordinate, the vector update preserves the original entry, while the state update preserves the corresponding register. Hence the vectors agree everywhere.
