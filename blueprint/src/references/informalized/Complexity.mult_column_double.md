<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_column_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Forms of the Product-Column Sum

**Claim.** For bit strings $a,b$ and each position $j$, summing products of bits at positions $p<|a|$ and $q<|b|$ with $p+q=j$ gives the product-column value at $j$, interpreting missing bits as zero.

**Proof.** Expand the outer sum over positions $p$ in $a$. For each fixed $p$, the row identity (Complexity.mult_column_row) evaluates the inner sum over positions $q$ in $b$: it is the product of the bit of $a$ at $p$ and the bit of $b$ at position $j-p$ when $p\le j$, and zero otherwise. Summing these row identities over all $p<|a|$ gives exactly the defining sum for the product-column value.

**Key facts.** `Complexity.mult_column_row`.
