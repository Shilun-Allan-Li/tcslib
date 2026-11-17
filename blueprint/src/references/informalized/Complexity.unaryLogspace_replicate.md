<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.unaryLogspace_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Query Languages

**Claim.** For the function $g(n)=1^n$, both the indexed-bit language and the index-below-length language belong to logarithmic space.

**Proof.** For a unary word of length $n$, the bit at index $i$ is $1$ exactly when $i<n$. Thus the condition defining the indexed-bit language is precisely the condition defining `ltLang`. The length condition is also $i<n$, so the index-below-length language is `ltLang` as well. Since `ltLang` belongs to logarithmic space (`ltLang_mem`), both languages do, and hence the required pair of membership statements holds.

**Key facts.** `Complexity.ltLang_mem`.
