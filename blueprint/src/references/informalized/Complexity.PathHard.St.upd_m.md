<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_m -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Square-Count Coordinate

**Claim.** Replacing the ninth coordinate of a state's register vector by $v$ gives the register vector of the state with its register for twice the square of the vertex count set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the ninth coordinate, both contain $v$, corresponding to the register for twice the square of the vertex count. At every other coordinate, neither update changes the original register. Therefore the vectors agree at all fifteen coordinates.
