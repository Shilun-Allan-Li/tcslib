<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Vertex-Count Coordinate

**Claim.** Replacing the eighth coordinate of a state's register vector by $v$ gives the register vector of the state with its register for twice the vertex count set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the eighth coordinate, both contain $v$, corresponding to the register for twice the vertex count. At every other coordinate, neither update changes the original register. Thus the vectors agree at all fifteen coordinates.
