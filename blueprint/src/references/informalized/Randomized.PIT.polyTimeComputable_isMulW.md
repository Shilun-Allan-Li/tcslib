<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_isMulW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Multiplication-Tag Recognition

**Claim.** The function returning $[1]$ when the second bit is $1$ and the third and fourth bits are $0$, and $[0]$ otherwise, is polynomial-time computable.

**Proof.** Each tested bit is available as a polynomial-time computable tag-bit function (`polyTimeComputable_tagBit`). Negating the tests at positions $2$ and $3$ preserves polynomial-time computability (`polyTimeComputable_not`). Conjoining the position-$1$ test with the negated position-$2$ test, then conjoining the negated position-$3$ test, gives the required predicate; conjunction preserves polynomial-time computability (`polyTimeComputable_and`).

**Key facts.** `Randomized.PIT.polyTimeComputable_tagBit`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`.
