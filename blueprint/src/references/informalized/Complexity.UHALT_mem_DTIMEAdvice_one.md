<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.UHALT_mem_DTIMEAdvice_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Halting with One-Bit Advice

**Claim.** For each machine representation scheme, the unary halting language is decidable in linear time with advice of length exactly one bit, using paired encodings of inputs and advice.

**Proof.** First, the unary halting language is contained in the all-ones language (`UHALT_le_allOnes`). The general advice theorem for any language contained in the all-ones language then gives a decider with advice of length exactly one bit and time bounded by a constant multiple of $n+1$ (`mem_DTIMEAdvice_one_of_le_allOnes`).

**Key facts.** `Complexity.UHALT_le_allOnes`, `Complexity.mem_DTIMEAdvice_one_of_le_allOnes`.
