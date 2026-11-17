<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multRows_column -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Column Equals Sum of Rows

**Claim.** For finite bit strings $a,b$ and a nonnegative integer $j$, the sum of the rows at indices $j,q$ over positions $q$ in $a$ equals the multiplication column at position $j$.

**Proof.** Expand each row as a sum over positions in $b$. The resulting double sum has one term for each pair of positions, and its condition is that the two positions add to $j$. The double-sum identity `Complexity.mult_column_double` identifies this sum with the multiplication column.

**Key facts.** `Complexity.mult_column_double`.
