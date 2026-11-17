<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.uniformProbability_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a complement

**Claim.** For a predicate on a finite nonempty set, the uniform probability that it fails is one minus the uniform probability that it holds.

**Proof.** At each point, the indicators of the predicate and its negation sum to $1$: exactly one of them holds. Averaging this pointwise identity over the finite uniform space shows that the two probabilities sum to the average of the constant function $1$, which is $1$. Rearranging gives the claim.
