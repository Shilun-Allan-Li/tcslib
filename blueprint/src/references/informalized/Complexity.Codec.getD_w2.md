<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean :: Complexity.Codec.getD_w2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit retrieval from nested pair encodings

**Claim.** For $i<|w'|$, the specified position in the nested pair encoding retrieves the bit at position $i$ of $w'$.

**Proof.** First rewrite the stated position as $2|x|+2+(2|w|+2+2i)$. Applying the second-component retrieval rule for pair encodings (`pe_getD_snd`) twice removes the outer pair and then the pair containing $w'$ and the remainder. The resulting lookup is at position $2i$ in the encoding of $w'$ with the remainder; the first-component retrieval rule (`pe_getD_fst`) identifies it with the lookup at $i$ in $w'$. The assumption $i<|w'|$ makes this the desired bit.

**Key facts.** `Complexity.Codec.pe_getD_snd`, `Complexity.Codec.pe_getD_fst`.
