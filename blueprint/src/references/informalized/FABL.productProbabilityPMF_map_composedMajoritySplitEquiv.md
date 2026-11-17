<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.productProbabilityPMF_map_composedMajoritySplitEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product law under a split-coordinate equivalence

**Claim.** The image of the product law on $2+(2m+1)$ biased signs under the split-coordinate equivalence is the law obtained by independently sampling the two blocks from their respective product distributions and pairing them.

**Proof.** It suffices to compare the masses at an arbitrary pair of blocks $x=(x_1,x_2)$. Under a finite equivalence, the mass of the image at $x$ is the original mass at its inverse image (\texttt{pmf\_map\_equiv\_apply}). The mass of the paired-block distribution is the product of the two block masses (\texttt{composedMajoritySplitPMF\_apply}). By the product-mass formula (\texttt{productProbabilityPMF\_apply}), the original mass is a product over all coordinates in the combined index set, while the two block masses give the products over the first and second blocks. The equivalence between the combined finite indices and the disjoint union of the two block index sets reindexes the full product as the product over that disjoint union; a product over a disjoint union factors into the products over its two summands. Thus the two masses agree for every pair of blocks, proving equality of the probability mass functions.

**Key facts.** `FABL.pmf_map_equiv_apply`, `FABL.composedMajoritySplitPMF_apply`, `FABL.productProbabilityPMF_apply`.
