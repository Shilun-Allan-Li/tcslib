<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.map_freeFrequencyReindex_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Frequency Reindexing

**Claim.** If a subset of a finite set $J$ is reindexed along the increasing bijection from $J$ to $\{0,\ldots,|J|-1\}$ and then mapped back along its inverse, the resulting subset is the original subset.

**Proof.** Membership in the mapped-back set is equivalent to membership of the image under the increasing bijection in the reindexed subset. By the definition of that reindexed subset, this is equivalent to membership in the original subset. The two subsets therefore have the same elements and are equal.
