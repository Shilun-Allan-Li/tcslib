<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expectRandomRestriction_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of random restriction expectation

**Claim.** The random restriction expectation of the pointwise sum of two functions equals the sum of their random restriction expectations.

**Proof.** Expand the random restriction expectation as a finite sum over free-coordinate sets, with each summand equal to its weight times the expectation over signs on the complementary coordinates. For each fixed free-coordinate set, expectation over the finite sign space preserves addition, so the expectation of the pointwise sum is the sum of the two expectations. Distribute the weight across that sum, then combine the finite sums term by term. This gives the sum of the two original random restriction expectations.
