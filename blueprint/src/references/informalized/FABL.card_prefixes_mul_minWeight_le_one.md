<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.card_prefixes_mul_minWeight_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Weight Cardinality Bound

**Claim.** For a family of prefixes whose associated restricted Fourier weights are all at least $c$, the family cardinality multiplied by $c$ is at most one.

**Proof.** Sum the lower bound $c\leq$ the associated restricted Fourier weight over all prefixes in $\mathcal A$. The map sending each prefix to its restriction inside $J$ is injective on $\mathcal A$, because every member of $\mathcal A$ is a subset of $J$ (`FABL.freeFrequencyPart_injOn_of_subsets`). Therefore this sum is exactly the sum of restricted weights over the corresponding family of typed prefixes. That total is at most one (`FABL.sum_restrictedFourierWeight_le_one`). Since the sum of the constant $c$ over $\mathcal A$ is $|\mathcal A|c$, the desired inequality follows.

**Key facts.** `FABL.freeFrequencyPart_injOn_of_subsets`, `FABL.sum_restrictedFourierWeight_le_one`.
