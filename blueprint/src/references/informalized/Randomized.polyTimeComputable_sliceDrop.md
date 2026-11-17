<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeComputable_sliceDrop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Suffix Truncation

**Claim.** For natural numbers $a$ and $k$, the function that decodes $z$ into components $x,y$ (using empty components if decoding fails) and returns the encoding of $x$ paired with the suffix of $y$ after dropping $a(|x|+1)^k$ bits is polynomial-time computable.

**Proof.** First construct a unary word whose length is $a(|x|+1)^k$, using the polynomial-time unary-word construction and composing it with the first-component decoder. Pair this word with the decoded second component. The pair's first component has exactly the required length, and its second component is $y$. Applying the polynomial-time prefix-dropping procedure to this pair therefore returns $y$ with its first $a(|x|+1)^k$ bits removed. Pair that suffix with the decoded first component. Pair encoding and composition preserve polynomial-time computability throughout, giving the claimed function.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.pairEncode`, `Turing.length_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.polyTimeComputable_dropPrefixByLen`.
