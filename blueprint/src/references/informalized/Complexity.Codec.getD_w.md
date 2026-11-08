<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.getD_w -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a bit from a nested encoding

**Claim.** For $i<|w|$, position $2|x|+2+2i$ in the encoding of $x$ paired with the encoding of $w$ paired with $r$ retrieves the bit at position $i$ of $w$, using false as the default.

**Proof.** The second-component retrieval rule for pair encodings (`pe_getD_snd`) removes the outer prefix and separator, reducing the lookup to position $2i$ in the encoding of $w$ paired with $r$. The first-component retrieval rule (`pe_getD_fst`) then identifies that position with the lookup at $i$ in $w$. Since $i<|w|$, this is the intended in-range bit.

**Key facts.** `Complexity.Codec.pe_getD_snd`, `Complexity.Codec.pe_getD_fst`.
