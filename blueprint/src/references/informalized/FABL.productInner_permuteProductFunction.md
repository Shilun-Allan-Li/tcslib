<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.productInner_permuteProductFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation Invariance of Product Inner Product

**Claim.** Applying the same permutation of coordinates to both functions leaves their product inner product unchanged under the independent product distribution with marginal $\pi$.

**Proof.** Expand the product inner product as a finite sum over inputs, and reindex that sum by the bijection which permutes the coordinates. At each input, the two function values in the summand are the original functions evaluated at the permuted input. The probability weight is unchanged by that coordinate permutation (`productProbabilityPMF_permuteProductInput`), since all coordinates have the same marginal and are independent. Consequently the reindexed sum is exactly the original product inner product.

**Key facts.** `FABL.productProbabilityPMF_permuteProductInput`.
