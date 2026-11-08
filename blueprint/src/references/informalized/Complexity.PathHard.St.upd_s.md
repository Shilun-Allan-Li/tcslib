<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Radius Coordinate

**Claim.** Replacing the sixth coordinate of a state's register vector by $v$ gives the register vector of the state with radius register set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the sixth coordinate, both contain $v$, corresponding to the radius register. At every other coordinate, the update leaves the original register unchanged on both sides. Thus the vectors agree at all fifteen coordinates.
