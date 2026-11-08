<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_headNil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time empty-head test

**Claim.** The function returning the one-bit list that records whether the first projection of $s$ is empty is polynomial-time computable.

**Proof.** The first projection is polynomial-time computable (`polyTimeComputable_pairFstD`). The test that returns a one-bit list recording whether its input is empty is polynomial-time computable (`polyTimeComputable_isNil`). Closure under composition (`PolyTimeComputable.comp`) therefore gives the claimed function.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_pairFstD`.
