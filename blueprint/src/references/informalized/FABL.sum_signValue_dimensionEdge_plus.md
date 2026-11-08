<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.sum_signValue_dimensionEdge_plus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Sum on a Dimension Edge

**Claim.** For a sign vector with coordinate $i$ equal to $1$, its total coordinate sign sum is $1$ plus the sign sum of the vector obtained by deleting coordinate $i$.

**Proof.** Decompose the sum into the contribution at coordinate $i$ and the contributions from all other coordinates. The former is $1$ by the edge condition; the latter, indexed after deleting $i$, is exactly the sign sum of the resulting vector. Their sum is the stated expression.
