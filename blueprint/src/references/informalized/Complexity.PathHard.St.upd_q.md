<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Width-Check Pointer

**Claim.** Replacing the eleventh coordinate of a state's register vector by $v$ gives the register vector of the state with width-check pointer set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the eleventh coordinate, both contain $v$, since this is the width-check pointer; at every other coordinate, the register remains its original value under both updates. Therefore the vectors agree at all fifteen coordinates.
