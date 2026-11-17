<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.mem_prefixLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Prefix Language

**Claim.** A bit string belongs to the prefix language exactly when there is a suffix completing the marker-dropped second projection to the prescribed length and producing a pair in $V$.

**Proof.** This is the defining membership condition of the prefix language: membership means that such a string $s$ exists, with the stated length equality and membership in $V$. The two sides are therefore identical conditions.
