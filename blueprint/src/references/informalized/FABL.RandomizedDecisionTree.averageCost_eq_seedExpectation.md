<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.averageCost_eq_seedExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost as Seed Expectation

**Claim.** Under independent inputs drawn from $\pi$, a randomized decision tree’s average query cost equals the seed expectation of the selected deterministic tree’s average query cost under the same input distribution.

**Proof.** Expand both sides as finite sums over inputs and seeds. Distributing the input sum across the seed expectation and then interchanging the order of summation gives the seed-weighted sum of the deterministic trees’ input-averaged query counts. The summands agree because the input and seed probabilities multiply the same query count, so this is precisely the claimed equality.
