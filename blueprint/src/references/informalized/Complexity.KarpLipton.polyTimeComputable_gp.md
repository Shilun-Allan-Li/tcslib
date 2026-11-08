<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.polyTimeComputable_gp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Second Projection Is Polynomial-Time

**Claim.** The function obtained by taking the second component of a parsed pair twice, with the empty string returned when parsing fails, is polynomial-time computable.

**Proof.** The second-projection function with the empty-string fallback is polynomial-time computable (`polyTimeComputable_pairSndD`). Polynomial-time computability is closed under composition (`PolyTimeComputable.comp`): composing that function with itself gives the repeated second projection. This composite is exactly the function in the claim.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`.
