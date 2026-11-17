<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.polyTimeComputable_gU -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Nested Projection

**Claim.** The function $g(z)=\pi_2(\pi_1(z))$, where the projections return the empty string on parse failure, is polynomial-time computable.

**Proof.** Each total pair projection is polynomial-time computable (`polyTimeComputable_pairFstD` and `polyTimeComputable_pairSndD`). The composition theorem for polynomial-time computable functions (`PolyTimeComputable.comp`) therefore shows that applying the first projection and then the second is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`.
