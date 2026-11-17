<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.monomial_eq_prod_tribeFrequencyPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial factorization across blocks

**Claim.** The monomial of $T$ on the full sign assignment equals the product, over blocks, of the monomials on the coordinates of $T$ within each block, evaluated on the corresponding input blocks.

**Proof.** Each coordinate in the array of size $sw$ belongs to exactly one block, so the union of the embedded blockwise frequency sets is exactly $T$ (`tribeFrequencyPart_biUnion`). These embedded sets are pairwise disjoint for distinct blocks (`disjoint_tribeOffsetEmbed`). Consequently, the product over $T$ factors as the product over blocks of the products over their embedded frequency sets. Reindexing each such product by the block's local coordinates identifies its factors with the signs in that block of the original assignment. This is the monomial of the blockwise frequency set evaluated on the corresponding input block, proving the claimed factorization.

**Key facts.** `FABL.tribeFrequencyPart_biUnion`, `FABL.disjoint_tribeOffsetEmbed`.
