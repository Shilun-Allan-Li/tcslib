<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean :: SubsetSumToPartition.SubsetSumToPartitionSoundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Subset Sum reduction

**Claim.** If the augmented Partition instance has a subset with the same total weight as its complement, then the original instance has a subset of weight $T$.

**Proof.** Let $W=\sum_a w(a)$, and let $S'$ be a subset witnessing equal partition. Let $S$ consist of the original elements whose corresponding left summands lie in $S'$. For any subset of the augmented universe, its weight splits into the weight of its original elements plus the contributions of whichever of the two dummy elements it contains. The same splitting applies to the complement, and the original weights on $S$ and $S^c$ sum to $W$. Now consider the four possibilities for membership of the two dummies. If both are in $S'$, or neither is, the equality of the two sides forces $W=0$; the bound $T\leq W$ then gives $T=0$, so the empty original subset works. If only the dummy of weight $2W-T$ is in $S'$, equality yields $\sum_{a\in S}w(a)=T$. If only the dummy of weight $W+T$ is in $S'$, equality yields $\sum_{a\in S^c}w(a)=T$. In each case an original subset of weight $T$ exists.
