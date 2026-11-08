<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLeft_ne_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Coordinate Embeddings

**Claim.** The images of the first and second coordinate blocks in the sum of blocks are distinct: for $i<a$ and $j<b$, the images of $i$ and $j$ cannot coincide.

**Proof.** Suppose the two images were equal and compare their natural-number values. The first image has value $i$, while the second has value $a+j$. Since $i<a$ and $j\ge 0$, we have $a+j\ge a>i$, a contradiction.
