<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3c_take_succ_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of successive prefixes

**Claim.** For finite binary strings $u,v$ and $j\in\mathbb{N}$, their prefixes of length $j+1$ agree exactly when their prefixes of length $j$ agree and their optional entries at index $j$ agree.

**Proof.** If the prefixes of length $j+1$ agree, taking their first $j$ entries shows that the length-$j$ prefixes agree, and reading entry $j$ from both equal prefixes shows that the optional entries agree. Conversely, a prefix of length $j+1$ consists of its first $j$ entries followed by its optional entry at index $j$. Agreement of those two parts therefore gives agreement of the full prefixes.
