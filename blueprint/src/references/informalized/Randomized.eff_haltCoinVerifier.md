<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.eff_haltCoinVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficiency of the halting coin verifier

**Claim.** The verifier that accepts when the fraction of true random bits lies strictly between the bounds determined by the input’s head length and depth runs in polynomial time in the verifier model.

**Proof.** The proof views the verifier as a one-input test on the self-delimiting encoding of the input and random string. The test `haltCoinTest` is polynomial-time computable ( `polyTimeComputable_haltCoinTest`), and on every pair encoding its output agrees with `haltCoinVerifier` (`haltCoinTest_pairEncode`). The general result that a polynomial-time test with this pair-encoding property yields an efficient Boolean verifier (`eff_boolVerifier_of_test`) therefore gives the claim.

**Key facts.** `Randomized.polyTimeComputable_haltCoinTest`, `Randomized.haltCoinTest_pairEncode`, `Randomized.eff_boolVerifier_of_test`.
