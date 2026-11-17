<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.eff_zeropVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficiency of the polynomial zero test verifier

**Claim.** The verifier that accepts if parsing fails or the parsed circuit is not well formed, and otherwise rejects exactly when the circuit’s randomized zero test accepts, runs in polynomial time in the verifier model.

**Proof.** Use `zeropW` as a test on the self-delimiting encoding of the input and random string. This test is polynomial-time computable (`polyTimeComputable_zeropW`), and its value on every pair encoding equals the value of `zeropVerifier` on that pair (`zeropW_pairEncode`). The general theorem converting such a polynomial-time test into an efficient Boolean verifier (`eff_boolVerifier_of_test`) gives the result.

**Key facts.** `Randomized.PIT.polyTimeComputable_zeropW`, `Randomized.PIT.zeropW_pairEncode`, `Randomized.eff_boolVerifier_of_test`.
