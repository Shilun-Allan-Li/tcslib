<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random Index Register Update

**Claim.** Replacing register 8 by $z$ gives the same register-value vector as updating coordinate 8 of the original vector to $z$.

**Proof.** At coordinate $8$, both vectors have value $z$, the new random index. For every other coordinate, both vectors have the original register value: the vector update leaves it unchanged, and modifying register 8 does not affect the other fields. Thus the vectors agree at all coordinates and are equal.
