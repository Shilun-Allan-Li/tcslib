<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.card_dimensionEdge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Cardinality of a sign-cube face

**Claim.** For any coordinate $i$ among $n$ coordinates, the sign vectors whose $i$th coordinate is $1$ form a set of cardinality $2^{n-1}$.

**Proof.** The sign vectors on the face where coordinate $i$ is fixed to $1$ are in bijection with a free sign at coordinate $i$ together with an arbitrary sign vector on the other $n-1$ coordinates. The free sign factor has cardinality $2$, while the other coordinates contribute $2^{n-1}$; hence the face has cardinality $2\cdot 2^{n-1}$, equivalently $2^n$. However the stated formal target is $2^{n-1}$, and the proof's equivalence and cardinality calculation as described in the source instead amount to $2^n$ if the fixed coordinate is counted as free. On the actual face, the coordinate is fixed, so only the other $n-1$ coordinates vary, giving $2^{n-1}$ as claimed.

**Caveat.** The supplied proof references `signProdDimensionEdgeEquiv`, whose definition is omitted from the upstream data. The proof manipulates a product cardinality and later counts all sign functions, so without that equivalence's statement the route cannot be fully reconstructed.
