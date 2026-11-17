<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_addresses -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addresses in a Nested Encoding

**Claim.** In the nested encoding of bit strings $a,b,c$, the positions specified in the statement retrieve the corresponding bits of $a$, $b$, and $c$, with out-of-range entries read as false.

**Proof.** The encoding of a pair places the first component in duplicated positions, then inserts a two-bit separator before the second component. The address formula for a first component (Complexity.pairEncode_getD) therefore gives the bit of $a$ at position $2i$ when $i<|a|$. For the second component, shift past the duplicated $a$ block and its separator using the shifted-address formula (Complexity.pairEncode_getD_snd), then apply the first-component formula to the inner encoding; at position $2|a|+2+2i$, this retrieves the $i$th bit of $b$ under the stated range condition. Finally, shifting past both the outer and inner prefixes applies the shifted-address formula twice, so every position $2|a|+2+2|b|+2+i$ retrieves the $i$th bit of $c$, including out-of-range positions under the default-false convention.

**Key facts.** `Complexity.pairEncode_getD`, `Complexity.pairEncode_getD_snd`.
