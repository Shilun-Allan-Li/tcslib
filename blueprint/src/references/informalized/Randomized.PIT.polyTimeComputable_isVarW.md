<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_isVarW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Variable-Tag Recognition

**Claim.** For every finite bit string, the function outputting $[b]$, where $b$ is true exactly when the bits at positions $1$, $2$, and $3$ are all false (with missing bits treated as false), is polynomial-time computable.

**Proof.** Each of the three tag-bit tests is polynomial-time computable (`polyTimeComputable_tagBit`). Negating each test preserves polynomial-time computability (`polyTimeComputable_not`); conjoining the first two negated tests and then the third gives exactly the condition that all three bits are false. Conjunction preserves polynomial-time computability (`polyTimeComputable_and`), so the resulting one-bit output is polynomial-time computable.

**Key facts.** `Randomized.PIT.polyTimeComputable_tagBit`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`.
