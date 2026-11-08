<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.eff_matchingVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficiency of the matching verifier

**Claim.** The Boolean verifier that applies the matching test to an input and a random bit string is efficient in the verifier model.

**Proof.** Use the polynomial-time matching test on the paired encoding of the input and random strings: the matching test is polynomial-time computable (polyTimeComputable_matchingTest), and on this encoding it returns exactly the verifier's Boolean output (matchingTest_pairEncode). The general theorem that a polynomial-time computable test agreeing with a verifier on paired inputs yields an efficient verifier (eff_boolVerifier_of_test) then gives the result.

**Key facts.** `Randomized.Matching.polyTimeComputable_matchingTest`, `Randomized.Matching.matchingTest_pairEncode`, `Randomized.eff_boolVerifier_of_test`.
