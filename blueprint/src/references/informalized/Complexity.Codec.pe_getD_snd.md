<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.pe_getD_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Second-Component Bit

**Claim.** For bit strings $u,v$ and any natural number $j$, the bit at position $2|u|+2+j$ in their self-delimiting pairing is the bit of $v$ at position $j$, interpreting positions past the end as false.

**Proof.** Apply the encoded-pair suffix-bit identity (`pairEncode_getD_snd`): after the doubled first component and its two-bit separator, the pairing agrees position by position with $v$.

**Key facts.** `Complexity.pairEncode_getD_snd`.
