<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.pe_getD_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a First-Component Bit

**Claim.** For bit strings $u,v$ and an index $i<|u|$, the bit at position $2i$ in their self-delimiting pairing is $u_i$.

**Proof.** The encoded-pair bit formula says that a position strictly before $2|u|$ reads from the first component at the position divided by two (`pairEncode_getD`). Since $i<|u|$, the position $2i$ is in this initial region, and $(2i)/2=i$. Thus the encoded bit is $u_i$.

**Key facts.** `Complexity.pairEncode_getD`.
