<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_11 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the scratch register

**Claim.** Updating coordinate $11$ of the register value vector to $y$ gives the value vector of the record with its scratch value for the copies and the power replaced by $y$.

**Proof.** Compare the two vectors at an arbitrary coordinate and consider each of the fifteen possibilities. At coordinate $11$, both sides equal $y$. At every other coordinate, the vector update and the record update both preserve the original coordinate. The vectors therefore agree everywhere.
