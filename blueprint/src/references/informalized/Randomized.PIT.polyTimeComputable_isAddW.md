<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_isAddW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Addition-Tag Recognition

**Claim.** The function returning $[1]$ when the second and fourth bits are $1$ and the third bit is $0$, and $[0]$ otherwise, is polynomial-time computable.

**Proof.** Each tested position is obtained by a polynomial-time computable tag-bit function (`polyTimeComputable_tagBit`). Negating the tests at positions $1$ and $3$ preserves polynomial-time computability (`polyTimeComputable_not`), and conjunction of polynomial-time computable Boolean predicates does as well (`polyTimeComputable_and`). Combining the negated position-$1$ test with the position-$2$ test, then conjoining the negated position-$3$ test, yields exactly the stated predicate, with its one-bit output.

**Key facts.** `Randomized.PIT.polyTimeComputable_tagBit`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`.
