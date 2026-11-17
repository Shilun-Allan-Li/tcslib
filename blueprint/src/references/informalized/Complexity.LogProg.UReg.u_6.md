<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_6 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Register Update

**Claim.** Replacing register 6 by $z$ gives the same register-value vector as updating coordinate 6 of the original vector to $z$.

**Proof.** Compare the two vectors at each coordinate. At coordinate $6$, both have value $z$, since this coordinate records the scratch-copy field. At every other coordinate, both retain the corresponding original register value. The vectors therefore agree everywhere and are equal.
