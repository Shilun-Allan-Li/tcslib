<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.existsUnique_frequency_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique Frequency Decomposition

**Claim.** Every finite frequency set $U$ splits uniquely into its part in $J$ and its part outside $J$, represented by a subset of $J$ and a finite set of indices outside $J$.

**Proof.** Take the proposed pair to be the free and fixed parts of $U$. Their lifted union is $U$ (`liftFreeFrequencyPart_union_liftFixedFrequencyPart`), so this pair gives a decomposition. For any other pair $(S,T)$ with the same union, test membership at each index in $J$: the fixed part cannot contain such an index, so membership in the union is exactly membership in the lift of $S$. Since the union is $U$, the characterization of membership in the free part (`mem_freeFrequencyPart`) shows that $S$ is the proposed free part. Next test an index outside $J$: the free part cannot contain it, so membership in the union is exactly membership in the lift of $T$. Membership in $U$ then identifies $T$ with the proposed fixed part by `mem_fixedFrequencyPart`. Both components are determined, proving uniqueness.

**Key facts.** `FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart`, `FABL.mem_freeFrequencyPart`, `FABL.mem_fixedFrequencyPart`.
