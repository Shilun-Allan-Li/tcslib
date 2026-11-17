<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_i -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Index Coordinate

**Claim.** Replacing the twelfth coordinate of a state's register vector by $v$ gives the register vector of the state with index register set to $v$.

**Proof.** To prove the two register vectors are equal, compare them coordinate by coordinate. At the twelfth coordinate, both contain $v$, since this is the index register; at every other coordinate, the update leaves the original register unchanged, and the state update leaves the corresponding register unchanged as well. Thus the vectors agree at all fifteen coordinates.
