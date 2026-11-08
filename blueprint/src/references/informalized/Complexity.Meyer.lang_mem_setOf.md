<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.lang_mem_setOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a predicate-defined language

**Claim.** A binary string belongs to the language defined by a predicate exactly when the predicate holds of that string.

**Proof.** By definition, the predicate-defined language consists precisely of the strings satisfying the predicate. Membership of $z$ in this language is therefore equivalent to $p(z)$.
