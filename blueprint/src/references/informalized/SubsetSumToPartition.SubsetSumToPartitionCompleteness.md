<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean :: SubsetSumToPartition.SubsetSumToPartitionCompleteness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Subset Sum reduction

**Claim.** If a subset of the original finite universe has total weight $T$, then the augmented instance produced by the reduction has a subset whose weight equals the weight of its complement.

**Proof.** Let $W=\sum_{a\in U}w(a)$, and suppose $S\subseteq U$ has weight $T$. Choose in the augmented universe the elements corresponding to $S$ together with the dummy of weight $2W-T$. The two parts are disjoint. The chosen subset has weight $T+(2W-T)=2W$. The total weight of the augmented universe is $W+(2W-T)+(W+T)=4W$. Since the sum over a subset and its complement is the total sum, the complement also has weight $2W$.
