<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Common Boundary

**Claim.** For four finite Boolean words and any position $j$, all four words have no symbol at position $j$ exactly when their maximum length is at most $j$.

**Proof.** A list has no symbol at position $j$ exactly when its length is at most $j$. Thus the condition for every one of the four words is equivalent to each of their lengths being at most $j$. The supremum of those lengths over the four indices is at most $j$ exactly when each length is at most $j$, giving the claim.
