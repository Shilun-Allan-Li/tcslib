<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.unary_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary languages lie in the all-ones language

**Claim.** For every set \(S\subseteq\mathbb N\), the unary language determined by \(S\) is contained in the all-ones language.

**Proof.** A string in the unary language satisfies, in particular, the condition that every entry is true. That is precisely membership in the all-ones language, so the containment follows.
