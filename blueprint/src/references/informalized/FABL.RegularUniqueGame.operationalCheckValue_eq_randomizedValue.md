<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.operationalCheckValue_eq_randomizedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operational and Randomized Check Values

**Claim.** The expected operational acceptance of a check, when each query position independently samples a uniform neighbor and uses that neighbor’s permuted response, equals the randomized value of the averaged neighbor function evaluated at the check’s queries.

**Proof.** Replace the check’s acceptance indicator on each tuple of responses by its multilinear extension evaluated at the corresponding sign values; these agree on sign inputs (`multilinearExtension_signValues`). The responses at the different query positions are independently sampled, so the expectation of this multilinear expression is the multilinear extension of the coordinatewise expected sign values (`pmfExpectation_multilinearExtension_productLaw`). At each position, the expected sign value of a neighbor response is the averaged neighbor function at that query (`pmfExpectation_neighborResponse`). Finally, the randomized value is the multilinear extension evaluated at those coordinate means (`SignPredicate.randomizedValue_eq_multilinearExtension`), giving the claimed equality.

**Key facts.** `FABL.RegularUniqueGame.multilinearExtension_signValues`, `FABL.RegularUniqueGame.pmfExpectation_multilinearExtension_productLaw`, `FABL.RegularUniqueGame.pmfExpectation_neighborResponse`, `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`.
