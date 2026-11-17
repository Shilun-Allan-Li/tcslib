<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.rp_error_reduction_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Error Reduction

**Claim.** A polynomial-time randomized verifier with polynomially many random bits, perfect rejection outside the language, and the stated inverse-polynomial acceptance guarantee on members can be amplified, for every $d$, to the stated exponentially small error while remaining polynomial-time.

**Proof.** Apply the general error-reduction theorem to the polynomial-time verifier model. Its closure under the repeated “any” test supplies the hypothesis required by that theorem; the theorem then yields the amplified verifier and its error bound. The polynomial-time conclusion follows because the closure fact is specifically for this model.

**Key facts.** `Randomized.polyTimeModel_closedUnderAny`, `Randomized.rp_error_reduction`.
