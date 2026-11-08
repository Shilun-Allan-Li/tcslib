<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposing the Packed Row

**Claim.** The packed encoding of all fields, with a prefix and trailer, splits at index $i$ into the encodings before $i$ followed by the encoding of field $i$ whose continuation contains all later fields and the trailer.

**Proof.** Split the list of fields into its first $i$ entries and the remainder. Since $i<l$, the remainder begins with `w i`, followed by the entries after $i$. The encoding distributes over list concatenation (`clFields_append`), so the encoding of the whole row becomes the encoding of the first part followed by the encoding of `w i` together with the encoding of the remaining part. Finally, concatenating the trailer into the continuation of the pair encoding is valid by the concatenation law for `pairEncode` (`clPair_append`). Associativity of list concatenation gives the stated equality.

**Key facts.** `Complexity.clFields_append`, `Complexity.clPair_append`.
