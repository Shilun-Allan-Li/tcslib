<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean :: Complexity.polyTimeComputable_blockAnyTest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Block Membership Test

**Claim.** The function that tests whether at least one of the specified blocks, paired with the parsed first component, belongs to $V$ is polynomial-time computable.

**Proof.** First construct a polynomial-time unary word of the required block length from the parsed first component, using the polynomial-time unary generator and composition with the first-component parser (`Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`). Pairing this word with itself and applying the polynomial-time XOR operation creates a mask that can be used to cancel a block's bits. The proof then feeds a suitably encoded input through the polynomial-time block XOR test (`Complexity.polyTimeComputable_blockXorAnyTest`), composing with the pair encoder as needed (`Complexity.PolyTimeComputable.pairEncode`). On the encoded input, the parsed first component and second component recover the intended $x$ and padded data (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). The XOR of each block with itself is the all-false word, so the block XOR test reduces exactly to membership testing of the original block paired with $x$; the list and length identities in the proof verify this reduction for every tested index (`Complexity.xorD_pairEncode`, `Complexity.zipWith_xor_self`, `Complexity.zipWith_xor_blockAt`). Thus its existential block test is precisely the function claimed.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_blockXorAnyTest`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.xorD_pairEncode`, `Complexity.zipWith_xor_self`, `Complexity.zipWith_xor_blockAt`.
