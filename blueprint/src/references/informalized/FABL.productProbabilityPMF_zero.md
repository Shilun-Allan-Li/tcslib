<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.productProbabilityPMF_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-coordinate product distribution

**Claim.** For a probability mass function on a finite set, the product distribution with zero coordinates is the point mass at the unique function from the empty index set to that set.

**Proof.** Two functions from the empty index set to the state space must agree, so every such function is the empty vector. It is therefore enough to compare the two probability masses at that vector. The product-mass formula (`productProbabilityPMF_apply`) expresses its mass as a product over no coordinates, hence as $1$. The point mass at the empty vector also has mass $1$ there, proving equality.

**Key facts.** `FABL.productProbabilityPMF_apply`.
