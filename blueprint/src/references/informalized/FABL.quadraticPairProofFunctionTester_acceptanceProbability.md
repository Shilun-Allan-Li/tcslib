<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairProofFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability Under Proof Reindexing

**Claim.** For any input word w and proof table P, the proof-function tester’s acceptance probability equals that of the quadratic-character pair tester on the linear and matrix functions extracted from P.

**Proof.** First, converting a tester’s Boolean answers to binary answers preserves its acceptance probability, with the tested function composed with the Boolean-to-binary correspondence (boolFunctionTesterOfF₂_acceptanceProbability). Reindexing the tester’s query domain likewise preserves the probability, while composing the tested function with the reindexing map (reindexDomainFunctionTester_acceptanceProbability). It remains to identify the resulting oracle pointwise. For a vector address, the reindexing selects the corresponding linear proof-table position, so the extracted linear function returns exactly the converted proof bit there. For a matrix address, it selects the matrix proof-table position indexed by the flattened matrix, so the extracted matrix function returns that converted proof bit. These two cases show that the reindexed input-and-proof word agrees everywhere with the oracle built from the two extracted functions; hence the acceptance probabilities are equal.

**Key facts.** `FABL.boolFunctionTesterOfF₂_acceptanceProbability`, `FABL.reindexDomainFunctionTester_acceptanceProbability`.
