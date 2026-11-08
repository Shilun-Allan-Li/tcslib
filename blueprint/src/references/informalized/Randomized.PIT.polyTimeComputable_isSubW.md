<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_isSubW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Subtraction-Tag Recognition

**Claim.** The function returning $[1]$ when the second, third, and fourth bits are all $1$, and $[0]$ otherwise, is polynomial-time computable.

**Proof.** The tag bits at positions $1$, $2$, and $3$ are polynomial-time computable (`polyTimeComputable_tagBit`). Negate the position-$1$ test to obtain the required zero bit (`polyTimeComputable_not`), then conjoin it with the positive tests at positions $2$ and $3$. Since conjunction preserves polynomial-time computability (`polyTimeComputable_and`), the resulting one-bit predicate is polynomial-time computable.

**Key facts.** `Randomized.PIT.polyTimeComputable_tagBit`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`.
