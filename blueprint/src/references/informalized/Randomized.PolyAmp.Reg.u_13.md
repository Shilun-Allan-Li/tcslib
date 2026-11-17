<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_13 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the scaling register

**Claim.** Updating coordinate $13$ of the register value vector to $y$ gives the value vector of the record with its scratch value for the scalings replaced by $y$.

**Proof.** Evaluate both vectors at an arbitrary coordinate and consider all fifteen cases. The values at coordinate $13$ are both $y$, while at all other coordinates the updates leave the original value in place. Thus the vectors agree coordinate by coordinate.
