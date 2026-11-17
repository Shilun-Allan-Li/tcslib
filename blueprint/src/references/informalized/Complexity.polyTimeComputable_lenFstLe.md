<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.polyTimeComputable_lenFstLe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded first-component length test

**Claim.** For each natural number $m$, the test that outputs $1$ exactly when the decoded first component has length at most $m$ is polynomial-time computable.

**Proof.** The constant function that outputs a word of length $m$ is polynomial-time computable. Pair it with the polynomial-time first projection, then apply the polynomial-time comparison test: that test outputs $1$ exactly when the second component’s length is at most the first component’s length. For the encoded pair consisting of the length-$m$ word and the projected input, this condition is precisely that the projected input has length at most $m$. The total projection convention also covers decoding failures, since the first projection then returns the empty word.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable.comp`, `Complexity.polyTimeComputable.pairEncode`, `Complexity.polyTimeComputable.comp`, `Complexity.polyTimeComputable.pairEncode`, `Complexity.polyTimeComputable.comp`, `Complexity.polyTimeComputable.pairEncode`, `Complexity.polyTimeComputable.comp`, `Complexity.polyTimeComputable.pairEncode`, `Complexity.polyTimeComputable.comp`, `Complexity.polyTimeComputable.pairEncode`, `Complexity.polyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_lenLe`, `Complexity.polyTimeComputable_pairFstD`.
