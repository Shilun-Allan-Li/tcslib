<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessCheck_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Access Check on Encoded Pairs

**Claim.** For bit strings $z$ and natural numbers $r,k$, the access check on the encoding of $z$ paired with the binary representation of $r$ returns `some (decide (r = k))`.

**Proof.** The decoder recovers exactly the two components of an encoded pair (`Turing.pairDecode_pairEncode`). The binary representation of $r$ is canonical (`Complexity.LogProg.canon_bits`), so the access check returns the Boolean test of whether that representation equals the binary representation of $k$. Injectivity of binary representation (`Complexity.LogProg.bits_injective`) makes this equality equivalent to $r=k$, giving the stated result.

**Key facts.** `Turing.pairDecode_pairEncode`, `Complexity.LogProg.canon_bits`, `Complexity.LogProg.bits_injective`.
