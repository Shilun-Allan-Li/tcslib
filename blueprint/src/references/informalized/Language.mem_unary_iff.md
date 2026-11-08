<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.mem_unary_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a Unary Language

**Claim.** A Boolean word belongs to the unary language determined by $S$ exactly when all its bits are true and its length belongs to $S$.

**Proof.** This is the defining membership condition for the unary language: membership is the conjunction of membership in the all-ones language and the condition that the word's length lies in $S$.
