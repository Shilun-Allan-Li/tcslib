<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.s_le_of_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound from Binary Word Width

**Claim.** If $y$ has positive length and the binary representation of $s$ is no longer than that of $|y|$, then $s\le 2|y|$.

**Proof.** The binary-width bound `bitsVal_le_of_width`, applied to the word of bits for $s$, the length $|y|$, and offset zero, gives that the value represented by those bits is at most $2|y|$. The hypothesis on binary widths supplies its width condition, and positive length supplies its positivity condition. Since the value of the binary representation of $s$ is $s$ (`bitsVal_bits`), the desired inequality follows.

**Key facts.** `Complexity.Codec.bitsVal_le_of_width`, `Complexity.LogProg.bitsVal_bits`.
