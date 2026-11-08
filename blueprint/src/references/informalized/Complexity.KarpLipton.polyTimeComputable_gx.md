<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.polyTimeComputable_gx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated First Projection Is Polynomial-Time

**Claim.** Taking the first component of a parsed pair twice, with the empty string returned whenever parsing fails, is polynomial-time computable.

**Proof.** The first-projection function with the empty-string fallback is polynomial-time computable (`polyTimeComputable_pairFstD`). Polynomial-time computability is closed under composition (`PolyTimeComputable.comp`), so composing this function with itself proves that the iterated first projection is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
