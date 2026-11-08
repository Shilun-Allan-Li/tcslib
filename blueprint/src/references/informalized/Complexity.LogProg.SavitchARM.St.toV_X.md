<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponent counter coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $2$ in its 18-entry register vector equals the value of its exponent counter $X$.

**Proof.** The exponent counter $X$ is the vector entry at index $2$. The index $r_X$ selects that entry, which is therefore equal to $X$.
