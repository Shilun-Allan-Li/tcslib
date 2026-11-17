<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.pairFstD_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First projection of an encoded pair

**Claim.** For any two finite bit strings $a$ and $b$, the total first projection of their self-delimiting pair encoding is $a$.

**Proof.** The decoder recovers the original pair from its self-delimiting encoding: `pairDecode_pairEncode` says that decoding the encoding of $(a,b)$ gives `some (a,b)`. Applying the first projection to this result and taking the default value in the total projection therefore returns $a$.

**Key facts.** `Turing.pairDecode_pairEncode`.
