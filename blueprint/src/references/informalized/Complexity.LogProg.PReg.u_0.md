<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Input-Pointer Register

**Claim.** Updating coordinate $0$ of a record's register vector to $z$ gives the vector of the record obtained by replacing its input-pointer register with $z$.

**Proof.** Compare the two vectors at an arbitrary coordinate. At coordinate $0$, the update assigns $z$, and the modified record's input-pointer coordinate is also $z$. At each other coordinate, the update leaves the original value unchanged, and replacing the input-pointer register leaves those other record fields unchanged. Thus the vectors agree at every coordinate.
