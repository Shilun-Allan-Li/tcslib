<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_candidateDecodingAssignmentLaw_edge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Edge Agreement Under Candidate Decoding

**Claim.** Under independent candidate decoding at each vertex, the expected indicator that a chosen edge satisfies its unique-game constraint equals the nested candidate average of the same agreement indicator, using the default label whenever a candidate set is empty.

**Proof.** The assignment law is a product of the individual vertex label laws. The endpoints of the edge are distinct, so averaging the agreement indicator under this product law reduces to successive averages over the source and target endpoint laws (`pmfExpectation_independentProductPMF_two_coordinates`). Each endpoint law is uniform on its candidate set when that set is nonempty and concentrated at the default otherwise. Replacing expectation under either such law by its finite candidate average, including the empty-set default case, identifies the resulting nested average with the candidate-decoding edge value (`pmfExpectation_finiteCandidatePMF`).

**Key facts.** `FABL.RegularUniqueGame.pmfExpectation_independentProductPMF_two_coordinates`, `FABL.RegularUniqueGame.pmfExpectation_finiteCandidatePMF`.
