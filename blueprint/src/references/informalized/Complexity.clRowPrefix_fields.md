<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRowPrefix_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Prefix as Packed Fields

**Claim.** For every $j\le l$, the stored row prefix of length $j$ equals the packed encoding of the first $j$ coordinate words in order.

**Proof.** Induct on $j$. At zero, both the stored prefix and the packed encoding of the empty initial segment are empty. For the successor step, the first $j+1$ coordinate words are the first $j$ words followed by coordinate $j$, by the list take-and-index decomposition. Packing respects concatenation (`Complexity.clFields_append`), so the packed encoding splits into the encoding of the first $j$ words followed by the encoding of coordinate $j$. By the induction hypothesis the first part is the stored prefix of length $j$; since $j<l$, the recursive definition of the stored prefix appends exactly the encoding of coordinate $j$.

**Key facts.** `Complexity.clFields_append`.
