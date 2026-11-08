<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.pmf_toReal_sum_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total probability mass

**Claim.** For a finite probability space, the real-valued masses assigned by its probability mass function sum to one.

**Proof.** Each mass is finite, so the real-valued conversion commutes with the finite sum of masses. Since the space is finite, that sum agrees with the corresponding sum over all points written as an infinite sum. A probability mass function has total mass one; converting this total to a real gives $1$.
