<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multColumn_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Column Bound

**Claim.** For finite bit strings $a,b$ and a nonnegative integer $j$, the multiplication column sum is at most the length of $a$.

**Proof.** Each summand is at most $1$: when $p\le j$, it is a product of two bits, and when $p>j$, it is $0$. Therefore the sum is bounded by the sum of $1$ over all positions in $a$. That sum is exactly the length of $a$.
