<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean :: SubsetSumToPartition.SubsetSumToPartitionReduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subset Sum reduces to Partition

**Claim.** Under the stated bound $T\leq\sum_a w(a)$, the original Subset Sum instance has a solution if and only if the augmented Partition instance has a solution.

**Proof.** The forward implication is the completeness statement: a subset of original weight $T$ yields an equal partition for the augmented weights ($\mathrm{SubsetSumToPartitionCompleteness}$). The reverse implication is the soundness statement: any equal partition for those augmented weights yields a subset of the original universe of weight $T$ ($\mathrm{SubsetSumToPartitionSoundness}$). Together these implications give the equivalence.

**Key facts.** `SubsetSumToPartition.SubsetSumToPartitionCompleteness`, `SubsetSumToPartition.SubsetSumToPartitionSoundness`.
