<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_injectiveLabelTuple_le_factorial_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Count of Injective Tuples

**Claim.** For a nonnegative weight on subsets, the sum of the weights of the image sets of injective $k$-tuples is at most $k!$ times the sum of the weights of all $k$-element subsets.

**Proof.** Encode each injective tuple by its image set together with the bijection from the labels to that image. This encoding is injective (`FABL.injectiveLabelTuple_code_injective`), so the tuple sum is the sum over a subset of all such labeled subsets. Since every weight is nonnegative, adding the remaining labeled subsets can only increase the sum. The sum over all labeled subsets is exactly $k!$ times the sum over the $k$-element subsets (`FABL.sum_injectiveLabelCodeTarget`), because each such subset has $k!$ bijective labelings. Combining these comparisons proves the bound.

**Key facts.** `FABL.injectiveLabelTuple_code_injective`, `FABL.sum_injectiveLabelCodeTarget`.
