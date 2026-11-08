<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.inCoRP_ZEROP_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Zero-Polynomial Testing

**Claim.** The language of encodings of nonempty, well-formed integer arithmetic circuits computing the zero polynomial belongs to coRP for the polynomial-time verifier model.

**Proof.** Apply the zero-polynomial coRP result to the polynomial-time verifier model. Its required efficiency hypothesis holds because the zero-testing verifier is efficient in that model. The resulting coRP membership is the claimed statement.

**Key facts.** `Randomized.eff_zeropVerifier`, `Randomized.inCoRP_ZEROP`.
