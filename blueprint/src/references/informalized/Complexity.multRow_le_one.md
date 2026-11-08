<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multRow_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Row Bound

**Claim.** For a bit $t$, a finite bit string $b$, and nonnegative integers $j,k$, the row sum is at most $1$.

**Proof.** The row sum equals $t$ times the bit of $b$ at position $j-k$ when $k\le j$, and is $0$ when $k>j$ (`Complexity.mult_column_row`). In the first case it is a product of bits and hence at most $1$; in the second case the bound is immediate.

**Key facts.** `Complexity.mult_column_row`.
