<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.expect_abs_signedHammingTwoTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute signed two-tail expectation

**Claim.** For $t\geq0$, the expected absolute difference between the upper-tail indicators at a sign vector and its negative is twice the expected upper-tail indicator.

**Proof.** Pointwise, the absolute difference of the two indicators equals their sum when $t\geq0$ (`abs_signedHammingTwoTail`). Taking expectations turns that sum into the sum of the two expectations. Negation preserves the uniform distribution on the sign cube, so the expected indicator evaluated at the negated vector equals the original expected indicator (`expect_hammingUpperTailIndicator_comp_neg`). The result follows by adding the two equal quantities.

**Key facts.** `FABL.abs_signedHammingTwoTail`, `FABL.expect_hammingUpperTailIndicator_comp_neg`.
