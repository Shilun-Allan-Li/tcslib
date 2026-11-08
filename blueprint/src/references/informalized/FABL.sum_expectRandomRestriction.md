<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_expectRandomRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of restriction expectation

**Claim.** The sum over a finite family of random restriction expectations equals the random restriction expectation of the pointwise sum of the family.

**Proof.** Expand each random restriction expectation as a finite sum over subsets $J$, weighted by the corresponding subset probability and averaged over sign assignments outside $J$. Interchange the two finite sums, first over family members and then over subsets. For each fixed $J$, expectation of a finite sum equals the sum of the expectations (`Finset.expect_sum_comm`); multiplying by the common subset weight distributes over that sum. Reassembling the terms over $J$ gives the random restriction expectation of the pointwise sum.
