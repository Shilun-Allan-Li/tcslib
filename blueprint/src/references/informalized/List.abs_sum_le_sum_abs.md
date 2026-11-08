<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.abs_sum_le_sum_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute value of a list sum

**Claim.** In a linearly ordered additive commutative group whose order is preserved by addition, the absolute value of the sum of a finite list is at most the sum of the absolute values of its entries.

**Proof.** Regard the list as a multiset, which preserves its sum and the sum of the absolute values of its entries. The multiset triangle inequality for absolute values then gives the claimed bound.
