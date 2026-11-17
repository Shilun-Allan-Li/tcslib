<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.monomial_freeFrequencyReindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial under frequency reindexing

**Claim.** The monomial on the reindexed set, evaluated at $y$, equals the monomial on $S$ evaluated at the assignment transferred to the coordinates of $J$.

**Proof.** The reindexed frequency set is the image of $S$ under the enumeration of $J$. The product over that image can therefore be reindexed as a product over $S$. Under the transferred assignment, the value at the enumerated position of each element of $S$ is exactly the value of $y$ at that position. Thus the factors agree term by term, and the two monomials are equal.
