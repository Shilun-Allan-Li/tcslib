<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_countdownNil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time nested empty-head test

**Claim.** The function returning the one-bit list that records whether the first projection of the second projection of $s$ is empty is polynomial-time computable.

**Proof.** The second projection of the parsed pair is polynomial-time computable (`polyTimeComputable_pairSndD`). Applying the polynomial-time empty-head test to that projection is polynomial-time computable by closure under composition (`PolyTimeComputable.comp`), giving the stated nested test.

**Key facts.** `Complexity.polyTimeComputable_headNil`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairSndD`.
