<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Width-Cap Coordinate

**Claim.** Replacing the tenth coordinate of a state's register vector by $v$ gives the register vector of the state with width-cap register set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the tenth coordinate, both contain $v$, since this is the width-cap register; at every other coordinate, the update leaves the original register unchanged, and the state update leaves the corresponding register unchanged. Hence the vectors agree at all fifteen coordinates.
