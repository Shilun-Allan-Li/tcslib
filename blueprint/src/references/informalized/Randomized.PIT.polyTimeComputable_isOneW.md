<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_isOneW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unit-Tag Recognition

**Claim.** The function returning $[1]$ when the second and third bits are $0$ and the fourth bit is $1$, and $[0]$ otherwise, is polynomial-time computable.

**Proof.** The tag bits at positions $1$, $2$, and $3$ are each polynomial-time computable (`polyTimeComputable_tagBit`). Negating the first two tests gives polynomial-time computable predicates for the required zero bits (`polyTimeComputable_not`). Conjoining these two predicates and then the positive test at position $3$ yields the unit-tag condition; conjunction preserves polynomial-time computability (`polyTimeComputable_and`).

**Key facts.** `Randomized.PIT.polyTimeComputable_tagBit`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`.
