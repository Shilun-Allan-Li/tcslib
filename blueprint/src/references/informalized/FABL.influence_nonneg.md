<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.influence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of influence

**Claim.** For every real-valued function on the cube and every coordinate, its influence is nonnegative.

**Proof.** Write the finite expectation defining influence as the sum of the squared discrete derivatives divided by the cardinality of the cube. Every squared term is nonnegative, and the cardinality is positive. Therefore the average, and hence the influence, is nonnegative.
