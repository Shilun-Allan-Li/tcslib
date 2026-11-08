<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.bpp_error_reduction_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Error Reduction

**Claim.** If a language has a polynomial-time randomized verifier with positive advantage over random guessing, then for every exponent parameter it has a polynomial-time verifier whose error is exponentially small in a polynomial of the input length.

**Proof.** By the polynomial-time model's closure under majority amplification (`polyTimeModel_closedUnderMajority`), the repeated-run majority verifier remains efficient. Apply the error-reduction theorem for models closed under majority (`bpp_error_reduction`) to the given weak verifier and the chosen exponent parameter. It supplies a verifier with the required strong success bound; the closure fact supplies its efficiency in the polynomial-time model.

**Key facts.** `Randomized.polyTimeModel_closedUnderMajority`, `Randomized.bpp_error_reduction`.
