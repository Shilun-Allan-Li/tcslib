<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_sliceDropAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Paired Suffix Slice

**Claim.** For every $a,k\in\mathbb{N}$, parse the total first and second projections of $z$, using the empty word for either projection when parsing fails; drop the first $a(|x|+1)^k$ bits of the second projection, where $x$ is the first projection; then encode the pair consisting of $x$ and the remaining suffix. This function is polynomial-time computable.

**Proof.** 1. First form the unary word of length $a(|x|+1)^k$, where $x$ is the total first projection of the input. Polynomial-time unary output composed with the polynomial-time first projection gives a polynomial-time function (`polyTimeComputable_polyUnary`, `PolyTimeComputable.comp`). Pairing that word with the total second projection preserves polynomial-time computability (`PolyTimeComputable.pairEncode`, `polyTimeComputable_pairSndD`).

2. On this encoded pair, apply the operation that drops from the second component as many bits as the length of the first component. By definition, this is the length-indexed prefix-drop operation. The encoding identities say that decoding the constructed encoding recovers exactly the unary word and the original second projection (`pairFstD_pairEncode`, `pairSndD_pairEncode`); since the unary word has the specified length, this operation drops exactly $a(|x|+1)^k$ bits. The prefix-drop operation is polynomial-time computable (`polyTimeComputable_dropPrefixByLength`), and polynomial-time functions are closed under composition (`PolyTimeComputable.comp`).

3. Finally, pair the original first projection with the resulting suffix. Both are polynomial-time computable, so the pairing closure theorem (`PolyTimeComputable.pairEncode`) proves that the full slice function is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.polyTimeComputable_dropPrefixByLength`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`.
