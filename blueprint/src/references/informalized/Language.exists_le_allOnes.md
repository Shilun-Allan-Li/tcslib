<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.exists_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Languages Restricted to All-Ones Strings

**Claim.** For every set $S$ of natural numbers, there is a language contained in the all-ones language such that the length-$n$ all-ones string belongs to it exactly when $n\in S$.

**Proof.** Take the unary language associated to $S$. It is contained in the all-ones language ( `Language.unary_le_allOnes`). The characterization of membership for unary strings states that the length-$n$ all-ones string belongs to this language exactly when $n\in S$ ( `Language.replicate_mem_unary_iff`).

**Key facts.** `Language.unary_le_allOnes`, `Language.replicate_mem_unary_iff`.
