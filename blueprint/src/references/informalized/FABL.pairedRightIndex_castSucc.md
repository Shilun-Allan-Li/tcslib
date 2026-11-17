<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedRightIndex_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Index Under Successor Embedding

**Claim.** The right index associated with the successor embedding of $j$ is the image, under the inclusion adding two coordinates, of the right index associated with $j$.

**Proof.** Both indices have the same coordinate value: replacing $j$ by its successor embedding increases its value by one, so the right-index formula gives $r+2(j+1)+1$; including the original right index in the larger coordinate set also gives $(r+2j+1)+2$. These expressions are equal, and hence the two finite indices agree.
