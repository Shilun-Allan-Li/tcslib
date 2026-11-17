<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_candidateDecodingAssignmentLaw_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Value of Candidate Decoding

**Claim.** The expected value of an independently candidate-decoded labeling in the finite unique-game instance equals the average of the candidate-decoding edge values over vertices and their neighbors.

**Proof.** For each labeling, its CSP value equals its average neighborhood success indicator (`neighborhoodSuccessValue_eq_cspValue`). Take expectation over the decoded labeling and interchange it with the finite average over vertices; then, inside each vertex term, interchange it with the average over neighbors. For each fixed vertex and neighbor, the expected success indicator under the assignment law is the candidate-decoding edge value (`pmfExpectation_candidateDecodingAssignmentLaw_edge`). The resulting average is precisely the candidate-decoding value by definition.

**Key facts.** `FABL.RegularUniqueGame.neighborhoodSuccessValue_eq_cspValue`, `FABL.fintypeExpectation_pmfExpectation_comm`, `FABL.RegularUniqueGame.pmfExpectation_candidateDecodingAssignmentLaw_edge`.
