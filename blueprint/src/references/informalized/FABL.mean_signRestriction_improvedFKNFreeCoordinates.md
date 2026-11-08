<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.mean_signRestriction_improvedFKNFreeCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Restricted Slice

**Claim.** The mean of the real-valued sign of the restriction of $g$, with coordinate $0$ fixed to $b$, equals the mean of the slice of $g$ obtained by fixing its first coordinate to $b$.

**Proof.** Reindex the free coordinates by the tail coordinates of the $(n+1)$-dimensional cube. The induced equivalence of function spaces preserves the uniform mean, so it suffices to compare the integrands at corresponding points. The restriction evaluation formula (`FABL.signRestriction_apply`) identifies the restricted value with $g$ evaluated at the combined free and fixed coordinates. The coordinate reconstruction identity (`FABL.combineSignCube_improvedFKNFreeCoordinates`) says that this combined point is exactly the point formed by placing the fixed sign in coordinate $0$ and the free tail after it. Thus the two integrands agree pointwise, giving equality of their means.

**Key facts.** `FABL.signRestriction_apply`, `FABL.combineSignCube_improvedFKNFreeCoordinates`.
