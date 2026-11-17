<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.polyTimeComputable_gu -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Projection Composition Is Polynomial-Time

**Claim.** The function that takes the second component of a parsed pair and then takes the first component twice, returning the empty string whenever a parse fails, is polynomial-time computable.

**Proof.** Both the first-projection and second-projection functions with the empty-string fallback are polynomial-time computable (`polyTimeComputable_pairFstD` and `polyTimeComputable_pairSndD`). Closure under composition (`PolyTimeComputable.comp`) first gives the composition of the second projection followed by one first projection, and then composing with the first projection again gives the stated function. These compositions preserve the specified empty-string behavior because they use the total projection functions themselves.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`.
