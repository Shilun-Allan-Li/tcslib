<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_p -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Pair-Scan Pointer

**Claim.** Replacing the second coordinate of a state's register vector by $v$ gives the register vector of the state with pair-scan pointer set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the second coordinate, both contain $v$, since this is the pair-scan pointer; at every other coordinate, the register remains its original value under both updates. Hence the vectors agree at all fifteen coordinates.
