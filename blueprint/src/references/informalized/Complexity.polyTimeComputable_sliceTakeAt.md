<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_sliceTakeAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Paired Prefix Slice

**Claim.** For every $a,k\in\mathbb{N}$, parse the total first and second projections of $z$, using the empty word for either projection when parsing fails; take the first $a(|x|+1)^k$ bits of the second projection, where $x$ is the first projection; then encode the pair consisting of $x$ and this prefix. This function is polynomial-time computable.

**Proof.** 1. Compute the unary word of length $a(|x|+1)^k$ from the total first projection $x$. Composing the polynomial-time unary-output function with the polynomial-time first projection gives a polynomial-time function (`polyTimeComputable_polyUnary`, `PolyTimeComputable.comp`). Pair this word with the total second projection; the pairing closure theorem shows this is polynomial-time computable (`PolyTimeComputable.pairEncode`, `polyTimeComputable_pairSndD`).

2. Apply the length-indexed prefix-take operation to that encoded pair. The encoding identities recover the unary word and the second projection, and the unary word's length is $a(|x|+1)^k$. Thus the operation takes exactly the desired prefix. The prefix-take operation is polynomial-time computable (`polyTimeComputable_takePrefixByLength`), and composition preserves polynomial-time computability (`PolyTimeComputable.comp`).

3. Encode the original first projection together with the resulting prefix. Both components are polynomial-time computable, so pairing closure proves the required function polynomial-time computable (`PolyTimeComputable.pairEncode`).

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.polyTimeComputable_takePrefixByLength`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`.
