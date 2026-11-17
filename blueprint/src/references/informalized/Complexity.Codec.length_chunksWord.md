<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_chunksWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a word of encoded cells

**Claim.** Concatenating the encodings of $f(0),\ldots,f(m-1)$ produces a word of length $Wm$.

**Proof.** There are $m$ cell encodings in the concatenation, and each has length $W$. The equal-length concatenation formula (`length_flatten_const`) therefore gives total length $Wm$.

**Key facts.** `Complexity.Codec.length_flatten_const`.
