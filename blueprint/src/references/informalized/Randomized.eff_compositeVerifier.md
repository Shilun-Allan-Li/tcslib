<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.eff_compositeVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficiency of the Composite Verifier

**Claim.** The composite verifier, which returns its Boolean decision as an optional Boolean, is efficient in the polynomial-time verifier model.

**Proof.** Apply the general efficiency result for Boolean tests to the test that computes the composite decision from a single encoded input. Its one-symbol output is polynomial-time computable (`Randomized.polyTimeComputable_compositeTest`). On every paired encoding, this test agrees with the composite verifier (`Randomized.compositeTest_pairEncode`). The general result therefore yields efficiency of the composite verifier (`Randomized.eff_boolVerifier_of_test`).

**Key facts.** `Randomized.polyTimeComputable_compositeTest`, `Randomized.compositeTest_pairEncode`, `Randomized.eff_boolVerifier_of_test`.
