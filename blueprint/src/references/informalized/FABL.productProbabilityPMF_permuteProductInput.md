<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.productProbabilityPMF_permuteProductInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation invariance of product inputs

**Claim.** For any permutation of the coordinate indices, the product distribution assigns the same mass to a tuple and to its permuted input.

**Proof.** The permuted input has coordinates $x(\sigma(i))$. By the product-mass formula (\texttt{productProbabilityPMF\_apply}), its mass is the product of $\pi(x(\sigma(i)))$ over all indices. Reindexing this finite product by the bijection $\sigma$ gives the product of $\pi(x(i))$ over all indices, which is the mass of the original input.

**Key facts.** `FABL.productProbabilityPMF_apply`.
