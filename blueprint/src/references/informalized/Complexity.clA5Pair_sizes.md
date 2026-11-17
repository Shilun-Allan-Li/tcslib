<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Pair_sizes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded Pair Length Bounds

**Claim.** For every bit string $w$, the first component selected from its decoded pair and the tail after one decoded-pair step each have length at most $|w|$.

**Proof.** First prove by strong induction on the length of a word that whenever decoding succeeds as a pair $(a,b)$, one has $|a|+|b|\le |w|$. Words of length zero or one cannot decode successfully. For a longer word, inspect its first two bits. If they are equal, successful decoding requires the remaining suffix to decode as some pair; apply the induction hypothesis to that shorter suffix. Decoding prepends the common bit to the first component, increasing its length by one, while the original word has two initial bits, so the sum of component lengths remains bounded by the word length. If the first two bits are false then true, decoding returns an empty first component and the remaining suffix as the second; the claimed inequality follows from the two-bit prefix. The other unequal prefix cannot decode. Now decode $w$ itself. If decoding fails, both selected outputs are empty. If it succeeds, the induction bound on the sum implies that each component separately has length at most $|w|$, which gives the two stated bounds.
