<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_10 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the coins register

**Claim.** Updating coordinate $10$ of the register value vector to $y$ gives the value vector of the record with its number of coins left replaced by $y$.

**Proof.** To prove equality of the two vectors, compare their values at an arbitrary coordinate $r$ and split into the fifteen possible coordinates. At coordinate $10$, both sides have value $y$; at every other coordinate, neither update changes the corresponding value. Hence the vectors agree coordinate by coordinate.
