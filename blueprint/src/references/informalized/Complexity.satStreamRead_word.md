<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRead_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seam-state encoding round trip

**Claim.** For every streaming seam state $s$, decoding its encoded word recovers its fresh-variable cursor, consumed input length, and grammar phase exactly.

**Proof.** Write $s$ as a state with fresh cursor $j$, consumed length $p$, and phase $q$. The encoded word nests pair encodings of unary strings for these three quantities. Pair decoding reverses each pair encoding, recovering each unary string exactly (pairDecode_pairEncode). Taking their lengths therefore recovers $j$, $p$, and the phase value $q$. The phase is a valid value below five, so reducing it modulo five leaves it unchanged. Hence all components of the state are recovered.

**Key facts.** `Turing.pairDecode_pairEncode`.
