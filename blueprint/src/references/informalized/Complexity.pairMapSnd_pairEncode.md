<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.pairMapSnd_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload map on an encoded pair

**Claim.** For any function $g$ from finite bit strings to finite bit strings and any finite bit strings $a$ and $b$, applying the threaded payload map of $g$ to the encoding of $(a,b)$ gives the encoding of $(a,g(b))$.

**Proof.** Decoding the self-delimiting encoding recovers the pair $(a,b)$, by `pairDecode_pairEncode`. The payload map therefore uses its defined-pair branch and re-encodes the first component unchanged while applying $g$ to the second. Its result is the encoding of $(a,g(b))$.

**Key facts.** `Turing.pairDecode_pairEncode`.
