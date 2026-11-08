<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.sum_signValue_dimensionEdge_minus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Sum After a Coordinate Flip

**Claim.** For a sign vector with coordinate $i$ equal to $1$, flipping that coordinate makes the sum of its coordinate signs equal to $-1$ plus the sign sum of the vector obtained by deleting coordinate $i$.

**Proof.** Decompose the sum over all coordinates into the contribution at $i$ and the sum over the remaining coordinates, indexed by the coordinates after deletion. The flip changes the sign at $i$ from $1$ to $-1$, while every other coordinate is unchanged. The remaining sum is precisely the sum of the deleted-coordinate vector, so the result follows.
