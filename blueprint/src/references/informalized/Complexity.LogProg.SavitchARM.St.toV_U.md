<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source code register coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $10$ in its 18-entry register vector equals the value of its current-node source-code register $U$.

**Proof.** The source-code register $U$ is the vector entry at index $10$. The index $r_U$ selects that entry, so the coordinate equals $U$.
