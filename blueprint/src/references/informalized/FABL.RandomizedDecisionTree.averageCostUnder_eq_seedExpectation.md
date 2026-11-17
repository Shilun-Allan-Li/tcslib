<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.RandomizedDecisionTree.averageCostUnder_eq_seedExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost as Seed Expectation

**Claim.** For a finite randomized decision tree and any probability distribution on the input space, its average query cost equals the seed expectation of the selected deterministic tree’s average query cost under that distribution.

**Proof.** Expand both sides using the finite-sum definition of expectation. On the left, the input distribution weights, for each input, the seed-averaged query count. Distributing this finite sum gives a sum over inputs and seeds of the same weights and query counts. Interchange the two finite sums; the result is the seed-weighted sum of each selected tree’s input-averaged query count, which is exactly the right-hand side. The individual summands agree by commutativity and associativity of real multiplication.
