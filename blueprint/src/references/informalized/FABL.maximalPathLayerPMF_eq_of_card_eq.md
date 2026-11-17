<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.maximalPathLayerPMF_eq_of_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal probabilities for equal-sized sets

**Claim.** If $A$ and $B$ are subsets of $\{0,\ldots,n-1\}$ with equal cardinality, then the random-permutation prefix distribution assigns them equal probability.

**Proof.** Choose a permutation $\tau$ carrying $A$ to $B$, which is possible because the sets have the same cardinality. Reindex the uniformly random permutations by right multiplication by $\tau^{-1}$; this is a bijection of the permutation space and so preserves the sum defining probability under the uniform law. The transport identity for maximal path prefixes (`maximalPathPrefix_mul_transport_eq_iff`) says precisely that a permutation has prefix $A$ if and only if its reindexed permutation has prefix $B$. Thus corresponding terms in the two probability sums agree, and the bijective reindexing shows the probabilities are equal.

**Key facts.** `FABL.maximalPathPrefix_mul_transport_eq_iff`.
