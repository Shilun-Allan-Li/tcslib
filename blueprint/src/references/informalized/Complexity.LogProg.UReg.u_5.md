<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_5 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target Register Update

**Claim.** Replacing register 5 by $z$ gives the same register-value vector as updating coordinate 5 of the original vector to $z$.

**Proof.** To prove the two vectors equal, compare their values at each coordinate. At coordinate $5$, the vector update returns $z$, which is also the target field of the modified register state. At each of the other fourteen coordinates, the vector update retains the original value, and changing the target field leaves those register fields unchanged. Thus the vectors agree at every coordinate and are equal.
