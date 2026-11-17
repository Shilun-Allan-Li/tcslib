<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_t -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Scratch Register

**Claim.** Replacing the fourth coordinate of a state's register vector by $v$ gives the register vector of the state with scratch register set to $v$.

**Proof.** Compare the two register vectors coordinate by coordinate. At the fourth coordinate, both contain $v$, corresponding to the scratch register. At every other coordinate, neither update changes the original register. Consequently the vectors agree at all fifteen coordinates.
