<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRows_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factoring a Row from the Stream

**Claim.** For every Boolean word appended after the first $N$ rows, the stream can be written as the first $j$ rows, followed by the packed encoding of row $j$, followed by a remainder.

**Proof.** Take the remainder to be the stream of the rows beginning at time $j+1$, through the remaining $N-(j+1)$ rows, followed by the given tail. Since $j<N$, we have $N=(j+1)+(N-(j+1))$. The decomposition of a stream at a sum of times (the row-addition law, `Complexity.clRows_add`) writes the first $N$ rows as the first $j+1$ rows followed by those remaining rows. By the recursive definition of the stream, its first $j+1$ rows are the first $j$ rows followed by the packed encoding of row $j$. Associativity of concatenation now gives the required factorization.

**Key facts.** `Complexity.clRows_add`.
