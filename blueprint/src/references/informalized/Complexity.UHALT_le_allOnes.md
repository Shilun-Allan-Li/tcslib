<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.UHALT_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Halting Language Inclusion

**Claim.** For every machine representation scheme, its unary halting language is contained in the language of all-ones strings.

**Proof.** The unary-language inclusion theorem states that every unary language over the Boolean alphabet is contained in the language of all-ones strings (`Language.unary_le_allOnes`). The unary halting language is defined as a unary language, so the theorem applies immediately.

**Key facts.** `Language.unary_le_allOnes`.
