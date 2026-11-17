<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.pairEncode_getD_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Component of a Pair Encoding

**Claim.** At position $2|u|+2+j$ in the pair encoding of $u$ and $v$, the defaulted bit equals the defaulted bit at position $j$ of $v$.

**Proof.** Apply the coordinate description of a pair encoding (`Complexity.pairEncode_getD`) at $2|u|+2+j$. This position is beyond both the doubled $u$ portion and the two separator positions, so the description reduces to the bit of $v$ at index $(2|u|+2+j)-2|u|-2$. Arithmetic simplifies this index to $j$, proving the equality.

**Key facts.** `Complexity.pairEncode_getD`.
