<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_7 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Count Register Update

**Claim.** Replacing register 7 by $z$ gives the same register-value vector as updating coordinate 7 of the original vector to $z$.

**Proof.** Compare the two vectors coordinate by coordinate. At coordinate $7$, both have value $z$, the new step count. At each other coordinate, the vector update preserves the old value, and the modified state has the same value in that register field as before. Hence the vectors are equal.
