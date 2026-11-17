<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPPIT.lean :: Randomized.pitVerifier_of_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier evaluation after decoding

**Claim.** When the two projections decode to circuits with the same number of input variables, the verifier returns false exactly according to the stated well-formedness and zero-test conditional.

**Proof.** Unfold the verifier and substitute the two assumed decode results into its case analysis. Both decoded circuits have the same input count, so the equality test on their counts succeeds. The verifier then evaluates its well-formedness conditional, which is exactly the conditional in the conclusion; the zero-test expression is consequently the same on both sides.
