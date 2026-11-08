<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.DTIMEAdvice_subset_PAdvicePoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Advice Class Inclusion

**Claim.** For all natural numbers $c,C,d$, every language decidable with advice of length $C(n+1)^d$ in time bounded by a constant multiple of $n^c+1$ belongs to the class of languages decidable with polynomially bounded advice and polynomial time.

**Proof.** Take a language in the stated advice class. By definition, the polynomial advice class is the union of these advice classes over all choices of the three natural-number parameters. The given language is already in the member indexed by $c,C,d$, so it belongs to that union.
