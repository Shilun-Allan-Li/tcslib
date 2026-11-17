<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.complete_structuralQueryProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structural query probability as expectation

**Claim.** Under the stated finite alphabet, distribution, and Fourier basis assumptions, the structural query probability of a coordinate equals the product-distribution probability that the tree queries it.

**Proof.** The structural query probability is equal to the deterministic query probability, by the theorem identifying these two quantities for a finite Fourier basis (`FABL.FiniteDecisionTree.deterministicQueryProbability_eq_structural`). The deterministic query probability is defined as the product-distribution expectation of the indicator that the tree queries the coordinate. Replacing the structural quantity by this equal deterministic quantity therefore gives exactly the asserted expectation.

**Key facts.** `FABL.FiniteDecisionTree.deterministicQueryProbability_eq_structural`.
