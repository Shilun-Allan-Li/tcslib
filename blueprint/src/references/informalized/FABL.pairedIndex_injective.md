<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedIndex_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Paired Coordinate Indices

**Claim.** The map sending each left or right copy of an index $j$ to $r+2j$ or $r+2j+1$, respectively, is injective.

**Proof.** Suppose two indices have the same image. If both are left indices, equality of their values gives $r+2i=r+2j$, hence $i=j$. If both are right indices, equality $r+2i+1=r+2j+1$ likewise gives $i=j$. If one is left and the other right, equality would make an even offset $2i$ equal to an odd offset $2j+1$, which is impossible. The same parity argument applies whichever index is listed first. Thus the two inputs must be equal in every possible case.
