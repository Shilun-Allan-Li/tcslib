<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.pmfExpectation_uniformSign_eq_average -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average over the Two Signs

**Claim.** For every function on the two signs, its expectation under their uniform distribution is the average of its values at $1$ and $-1$.

**Proof.** Replace the probability expectation by the uniform average (`pmfExpectation_uniformPMF_eq_expect`). The uniform average is the sum over all signs divided by the number of signs; the sum of the function over the two signs is $g(1)+g(-1)$ (`sum_sign_eq`). Since there are exactly two signs, division by their cardinality gives $(g(1)+g(-1))/2$.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.sum_sign_eq`.
