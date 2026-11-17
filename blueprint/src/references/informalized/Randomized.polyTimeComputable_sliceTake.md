<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeComputable_sliceTake -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Truncation

**Claim.** For all natural numbers $a$ and $k$, the function that decodes a bit string into components $x$ and $y$ (using empty components if decoding fails) and returns the encoding of $x$ with the prefix of $y$ of length $a(|x|+1)^k$ is polynomial-time computable.

**Proof.** First compute the decoded first component, then use it to generate a string of $a(|x|+1)^k$ true bits. This unary polynomial-length function is polynomial-time computable, and composing it with first-component decoding shows that the required length string can be produced in polynomial time. Pairing that string with the decoded second component remains polynomial-time computable. The prefix-by-length operation extracts a prefix whose length is the length of its first decoded component. On the constructed encoding, decoding recovers exactly the generated length string and the original second component, so this operation returns the second component truncated to length $a(|x|+1)^k$. Finally, pair this result with the decoded first component. Polynomial-time computability is preserved under composition and under pairing polynomial-time computable functions, giving the claimed function.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairSndD`, `Randomized.polyTimeComputable_takePrefixByLen`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
