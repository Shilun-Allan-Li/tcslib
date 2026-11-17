<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedOperationalCheckValue_eq_randomizedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operational and averaged check values

**Claim.** For a regular unique game, bounded function table, vertex, and randomized sign query check, the operational value—averaging over independent uniform neighbor choices at the query positions—equals the randomized value of the check applied to the function obtained by averaging the neighbor-transformed table functions at that vertex.

**Proof.** First express the randomized value of a sign predicate as its multilinear extension evaluated at the vector of input means (`SignPredicate.randomizedValue_eq_multilinearExtension`). Thus the operational value is the expectation, over independent uniform neighbor choices, of the predicate’s multilinear extension applied to the corresponding transformed table values. The product-law identity for expectations of multilinear extensions (`pmfExpectation_multilinearExtension_productLaw`) moves this expectation inside each coordinate of the extension, replacing each transformed table value by its expectation over a uniform neighbor. Uniform expectation agrees with the finite uniform average (`pmfExpectation_uniformPMF_eq_expect`), which is exactly the averaged neighbor function at the queried point. Applying the same representation of randomized value once more identifies the resulting multilinear extension with the randomized value of the averaged function.

**Key facts.** `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`, `FABL.RegularUniqueGame.pmfExpectation_multilinearExtension_productLaw`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`.
