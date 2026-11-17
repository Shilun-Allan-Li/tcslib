<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the shift register

**Claim.** Replacing coordinate $14$ of the register vector by $v$ gives the vector of the state obtained by replacing its shift register $z$ by $v$.

**Proof.** At coordinate $14$, both constructions give the new value $v$. At each of the other fourteen coordinates, the vector update leaves the entry alone and the state update leaves the corresponding register alone. The resulting vectors are therefore equal at every coordinate.
