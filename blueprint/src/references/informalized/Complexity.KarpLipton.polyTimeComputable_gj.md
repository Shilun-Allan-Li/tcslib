<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.polyTimeComputable_gj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Triple Projection

**Claim.** The function $g(z)=\pi_2(\pi_1(\pi_2(z)))$, with total pair projections returning the empty string when parsing fails, is polynomial-time computable.

**Proof.** Apply the polynomial-time composition theorem twice (`PolyTimeComputable.comp`). First, composing the second projection with the first projection gives a polynomial-time computable function. Composing that result with the outer second projection shows that the full nested projection is polynomial-time computable. The required polynomial-time computability of each projection is supplied by `polyTimeComputable_pairFstD` and `polyTimeComputable_pairSndD`.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.comp`.
