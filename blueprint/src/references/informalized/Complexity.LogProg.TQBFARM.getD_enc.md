<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.getD_enc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit Positions in an Encoded Pair

**Claim.** For an input encoding the pair of $q$ and the serialization of $\varphi$, each bit position lies either in the doubled encoding of $q$, at the pair separator, or in the serialized formula tail, with the specified bit value in each case.

**Proof.** Substitute the assumed pair encoding for $x$ and apply the bit-position formula for a paired encoding (\texttt{Complexity.pairEncode_getD}). It gives the doubled-prefix case, the false and true separator bits, and the shifted tail index, using false for positions beyond the input.

**Key facts.** `Complexity.pairEncode_getD`.
