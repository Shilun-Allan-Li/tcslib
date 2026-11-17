<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_neighborResponse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Neighbor Response

**Claim.** For each vertex and query, the uniform expectation over its neighbors of the table's sign response at the permuted query equals the averaged neighbor function evaluated at that query.

**Proof.** The expectation of a function under the uniform law on a finite nonempty set is its uniform finite average (`pmfExpectation_uniformPMF_eq_expect`). Apply this to the sign response over the neighbors. By the definition of the averaged neighbor function, that same average is its value at the given query, so the two sides agree.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
