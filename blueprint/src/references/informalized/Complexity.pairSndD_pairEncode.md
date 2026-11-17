<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.pairSndD_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second projection of an encoded pair

**Claim.** For any finite bit strings $a$ and $b$, the total second projection of their self-delimiting pair encoding is $b$.

**Proof.** The decoder recovers the original pair from its encoding, so `pairDecode_pairEncode` gives `some (a,b)`. Taking the second projection and then the default value in the total projection returns $b$.

**Key facts.** `Turing.pairDecode_pairEncode`.
