<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Input Pointer

**Claim.** Updating coordinate $0$ of the ordered register vector to $z$ gives the vector of the record whose input pointer has been replaced by $z$.

**Proof.** Compare the two vectors at each coordinate. At coordinate $0$, both have value $z$, since this is the input-pointer field. At every other coordinate, the update leaves the vector unchanged, and replacing the input pointer in the record leaves all other fields unchanged. Thus the vectors agree at every coordinate and are equal.
