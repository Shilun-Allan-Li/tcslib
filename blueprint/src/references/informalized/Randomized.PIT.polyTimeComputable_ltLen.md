<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_ltLen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Comparison

**Claim.** If $f$ and $g$ are polynomial-time computable, then the one-bit output indicating whether $|f(D)|<|g(D)|$ is polynomial-time computable.

**Proof.** First compute the encoded pair of outputs $(f(D),g(D))$ using the closure of polynomial-time computability under pairing (`Complexity.PolyTimeComputable.pairEncode`). Apply the polynomial-time length comparison that returns whether the second decoded component has length at most the first (`Complexity.polyTimeComputable_lenLe`). Since decoding this encoding recovers $f(D)$ and $g(D)$, this test says $|g(D)|\le |f(D)|$. Complementing its one-bit answer, using closure under Boolean negation (`Complexity.polyTimeComputable_not`), gives the desired test: for natural-number lengths, the negation of $|g(D)|\le |f(D)|$ is exactly $|f(D)|<|g(D)|$.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_lenLe`, `Complexity.polyTimeComputable_not`.
