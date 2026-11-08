<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_12 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the digit-count register

**Claim.** Updating coordinate $12$ of the register value vector to $y$ gives the value vector of the record with its scratch value for the digit count and comparison replaced by $y$.

**Proof.** Check equality at an arbitrary coordinate by splitting into the fifteen coordinates. At coordinate $12$, both sides have value $y$; at each remaining coordinate, both updates preserve the original value. This establishes equality of the vectors.
