<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Vertex Count

**Claim.** Updating coordinate $1$ of the ordered register vector to $z$ gives the vector of the record whose vertex count has been replaced by $z$.

**Proof.** At coordinate $1$, both vectors have value $z$, the replaced vertex-count field. At every other coordinate, the vector update leaves the value unchanged, just as replacing the vertex count leaves the other fields of the record unchanged. Hence the two vectors agree at every coordinate and are equal.
